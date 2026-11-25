-- Prove2me | solution 1 for PI.OddDualWeyl.dir1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:06:28.600799+00:00
-- url     : https://prove2.me/submissions/4f4cbf8b-5c4c-40e9-b5cb-31a29e5a68dd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_RevColOneTranspose
import Theorems.Thm_PI_OddDualWeyl_antitone_lamStar
import Theorems.Thm_PI_OddDualWeyl_isUnit_invT
import Theorems.Thm_PI_OddDualWeyl_invT_invT
import Theorems.Thm_PI_OddDualWeyl_sgn_zpow_pm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial Matrix
noncomputable section
namespace PI.OddDualWeyl
section Lin
variable {R : Type} [CommRing R] {k M : ℕ}
end Lin
section Top
variable {K : Type} [Field K]
private theorem eq_of_rel_of_isHomogeneous_of_uniq (hU : Uniq) {m M D : ℕ}
    {F F₁ F₂ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K}
    (h₁ : Rel K (m + 1) M F F₁) (h₂ : Rel K (m + 1) M F F₂)
    (d₁ : IsHomogeneous F₁ D) (d₂ : IsHomogeneous F₂ D) : F₁ = F₂ := by
  unfold Rel at h₁ h₂
  have hd : IsHomogeneous (F₁ - F₂) D := by
    rw [← mem_homogeneousSubmodule] at d₁ d₂ ⊢
    exact Submodule.sub_mem _ d₁ d₂
  have h0 : dualSub K (m + 1) (F₁ - F₂) = 0 := by
    rw [map_sub, h₁, h₂, sub_self]
  exact sub_eq_zero.mp (hU K (m + 1) D (F₁ - F₂) hd h0)
end Top
end PI.OddDualWeyl
end
end

set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
variable {K : Type} [Field K]
namespace PI.OddDualWeyl
theorem _root_.solution (hC : ∀ (R : Type) [CommRing R] (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam →
      ∀ f ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf lam), ∃ f' ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)),
        Rel R (m + 1) (expM lam) f f')
    (hH : HomW) (hB : Bk) (hE : EV) (hU : Uniq) (hDB : DualB) (hS : SgnPM) (hG : GStep)
    (O : Type) [CommRing O] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det) :
    ∀ F ∈ Dl0 O m lam (colSpan O g), ∃ F' ∈ Dl0 O m (lamStar lam) (colSpan O (g⁻¹)ᵀ),
      ∀ z : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsUnit z.det →
        z.det ^ lam (Fin.last m) * eval (fun x => z x.1 x.2) F =
          (revCol (z⁻¹)ᵀ).det ^ lamStar lam (Fin.last m) * eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) F' := by
  intro F hF
  by_cases hl : Antitone lam
  swap
  · unfold Dl0 at hF
    rw [if_neg hl, Submodule.mem_bot] at hF
    subst hF
    exact ⟨0, Submodule.zero_mem _, fun z _ => by simp⟩
  have hl' := antitone_lamStar hl
  unfold Dl0 at hF
  rw [if_pos hl] at hF
  simp only [Submodule.mem_iInf] at hF
  have hbal := hB m lam hl
  have hhom : ∀ f' ∈ weyl O (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)),
      IsHomogeneous f' (degW (nuOf (lamStar lam))) :=
    fun f' hf' => hH O (m + 1) _ f' hf'
  obtain ⟨F', -, hrel, hF'hom⟩ := hG O K m lam g hg hbal hhom (hC O m lam hl) F (hF g ⟨hg, rfl⟩)
  have hF'lat : F' ∈ Dl0 O m (lamStar lam) (colSpan O (g⁻¹)ᵀ) := by
    unfold Dl0
    rw [if_pos hl']
    simp only [Submodule.mem_iInf]
    rintro g' ⟨hg', hspan⟩
    have hh : IsUnit ((g'⁻¹)ᵀ).det := isUnit_invT hg'
    have hspan' : colSpan O g = colSpan O (g'⁻¹)ᵀ := by
      have := hDB O K m (g⁻¹)ᵀ g' (isUnit_invT hg) hg' hspan
      rwa [invT_invT hg] at this
    obtain ⟨F'', hF''mem, hrel'', hF''hom⟩ :=
      hG O K m lam (g'⁻¹)ᵀ hh hbal hhom (hC O m lam hl) F (hF _ ⟨hh, hspan'⟩)
    rw [invT_invT hg'] at hF''mem
    rw [eq_of_rel_of_isHomogeneous_of_uniq hU hrel hrel'' hF'hom hF''hom]
    exact hF''mem
  refine ⟨C (sgnK K m ^ lamStar lam (Fin.last m)) * F', ?_,
    fun z hz => hE K m _ _ _ _ F F' hbal hrel hF'hom z hz⟩
  rcases sgn_zpow_pm (K := K) hS m (lamStar lam (Fin.last m)) with h | h
  · rw [h, C_1, one_mul]
    exact hF'lat
  · rw [h, C_neg, C_1, neg_one_mul]
    exact Submodule.neg_mem _ hF'lat
end PI.OddDualWeyl

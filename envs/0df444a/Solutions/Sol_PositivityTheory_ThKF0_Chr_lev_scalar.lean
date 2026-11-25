-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.lev_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:35:14.537319+00:00
-- url     : https://prove2.me/submissions/58b3f629-b2e3-4203-8acd-ed1df94b37fc

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_BoxCancel
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_DoublingGramFromBlocks
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ExistsDoubledUnitaryBlock
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_uniq
import Theorems.Thm_PositivityTheory_ThKF0_Chr_IsSp_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Chr
open Matrix GlobalTheory.WeilM PositivityTheory.ThK.SiegelT
variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β β₁ ν κ κ₁ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype β₁] [DecidableEq β₁]
  [Fintype ν] [DecidableEq ν] [Fintype κ] [Fintype κ₁] {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E}
  {JA : Matrix α α E} {J : Matrix β β E} {J₁ : Matrix β₁ β₁ E} {ι : Matrix β β₁ E} {X : Matrix β ν E}
  {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} {e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)}
omit [DecidableEq α]
namespace PositivityTheory.ThKF0.Chr
theorem _root_.solution (h : Ax C ψ) (hS : IsSp S) (hj : Function.Injective j) (he : IsE C ψ S j e)
    {d : Darboux (symp c ξ JA J) κ} {d₁ : Darboux (symp c ξ JA J₁) κ₁}
    (hrel : ∀ u z, Rel S j (d.e u) (d₁.e z) ↔ ∃ a : Matrix α ν E, u = z * ιᵀ + a * Xᵀ)
    {om : UG c J →* Module.End ℂ ((κ → R) → ℂ)} {om₁ : UG c J₁ →* Module.End ℂ ((κ₁ → R) → ℂ)}
    (hs : IsSplitting C ψ d (actB c) om) (hs₁ : IsSplitting C ψ d₁ (actB c) om₁)
    (m : UG c J) (g : UG c J₁) (t : Matrix ν ν E) (h1 : m.1.1 * ι = ι * g.1.1) (h2 : m.1.1 * X = X * t) :
    ∃ a : ℂ, ∀ φ ∈ C.sp κ, e (om m φ) = a • om₁ g (e φ) := by
  obtain ⟨a, ha⟩ := h.uniq hS hj he (e' := om₁ g⁻¹ ∘ₗ e ∘ₗ om m) (fun w w₁ hw φ hφ => by
    obtain ⟨u, rfl⟩ := d.e.surjective w
    obtain ⟨z, rfl⟩ := d₁.e.surjective w₁
    obtain ⟨b, rfl⟩ := (hrel u z).1 hw
    have r := (hrel (actB c m (z * ιᵀ + b * Xᵀ)) (actB c g z)).2 ⟨b * tᵀ, by
      simp only [actB, Matrix.add_mul, Matrix.mul_assoc, ← transpose_mul, h1, h2]⟩
    show om₁ g⁻¹ (e (om m (d.rho ψ _ φ))) = d₁.rho ψ z (om₁ g⁻¹ (e (om m φ)))
    rw [hs.impl _ _ _ hφ, Darboux.rho, he.law _ _ r _ (hs.pres _ _ hφ)]
    refine (hs₁.impl g⁻¹ _ _ (he.maps _ (hs.pres _ _ hφ))).trans ?_
    congr 1
    simp [actB, Matrix.mul_assoc, ← transpose_mul]) (hs.adm m _ (he.adm _ (hs₁.adm g⁻¹ _ (h.ev0 _))))
  refine ⟨a, fun φ hφ => ?_⟩
  rw [← map_smul, ← ha φ hφ]
  show _ = (om₁ g * om₁ g⁻¹) _
  rw [← map_mul, mul_inv_cancel, map_one]
  rfl
end PositivityTheory.ThKF0.Chr

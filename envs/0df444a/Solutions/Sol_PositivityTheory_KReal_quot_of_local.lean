-- Prove2me | solution 1 for PositivityTheory.KReal.quot_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:30:19.864881+00:00
-- url     : https://prove2.me/submissions/d25b02b6-9b1e-4641-84ee-d9efc62df7ed

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasGl
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreMain
import Theorems.Thm_PositivityTheory_KReal_exists_factor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
namespace PositivityTheory.KReal
theorem _root_.solution {J M T T' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup T] [Module ℂ T]
    [AddCommGroup T'] [Module ℂ T'] [Nontrivial T] [Nontrivial T']
    (actM : J → Module.End ℂ M) (act : J → Module.End ℂ T) (act' : J → Module.End ℂ T')
    (R : Submodule ℂ M) (hR : R ≠ ⊤)
    (hN : ∀ N : Submodule ℂ M, (∀ W, ∀ x ∈ N, actM W x ∈ N) → N ≠ ⊤ → N ≤ R)
    (φ : M →ₗ[ℂ] T) (φ' : M →ₗ[ℂ] T') (hφ : Function.Surjective φ) (hφ' : Function.Surjective φ')
    (e : ∀ W x, φ (actM W x) = act W (φ x)) (e' : ∀ W x, φ' (actM W x) = act' W (φ' x)) :
    ∃ (Pi : Type) (_ : AddCommGroup Pi) (_ : Module ℂ Pi) (actP : J → Module.End ℂ Pi)
      (π : T →ₗ[ℂ] Pi) (π' : T' →ₗ[ℂ] Pi), Function.Surjective π ∧ Function.Surjective π' ∧
      (∀ W x, π (act W x) = actP W (π x)) ∧ (∀ W x, π' (act' W x) = actP W (π' x)) ∧ Nontrivial Pi ∧
      ∀ N : Submodule ℂ Pi, (∀ W, ∀ x ∈ N, actP W x ∈ N) → N = ⊥ ∨ N = ⊤ := by
  classical
  set S : Set (Submodule ℂ M) := {N | (∀ W, ∀ x ∈ N, actM W x ∈ N) ∧ N ≠ ⊤} with hS
  set Rm : Submodule ℂ M := sSup S with hRm
  have hRmR : Rm ≤ R := sSup_le fun N' hN' => hN N' hN'.1 hN'.2
  have hRmtop : Rm ≠ ⊤ := fun h => hR (top_le_iff.mp (h ▸ hRmR))
  have hRst : ∀ W, ∀ x ∈ Rm, actM W x ∈ Rm := by
    intro W
    have hle : Rm ≤ Rm.comap (actM W) :=
      sSup_le fun N hN x hx => (le_sSup hN : N ≤ Rm) (hN.1 W x hx)
    exact fun x hx => hle hx
  have hker : ∀ {T₀ : Type} [AddCommGroup T₀] [Module ℂ T₀] [Nontrivial T₀]
      (act₀ : J → Module.End ℂ T₀) (ψ : M →ₗ[ℂ] T₀), Function.Surjective ψ →
      (∀ W x, ψ (actM W x) = act₀ W (ψ x)) → LinearMap.ker ψ ≤ Rm := by
    intro T₀ _ _ _ act₀ ψ hψ eψ
    refine le_sSup ⟨fun W x hx => ?_, fun htop => ?_⟩
    · rw [LinearMap.mem_ker] at hx ⊢
      rw [eψ, hx, map_zero]
    · obtain ⟨y, hy⟩ := exists_ne (0 : T₀)
      obtain ⟨m, rfl⟩ := hψ y
      exact hy (LinearMap.mem_ker.mp (htop ▸ Submodule.mem_top))
  let actP : J → Module.End ℂ (M ⧸ Rm) := fun W => Rm.mapQ Rm (actM W) (fun x hx => hRst W x hx)
  obtain ⟨π, hπ⟩ := exists_factor φ hφ Rm.mkQ (by simpa using hker act φ hφ e)
  obtain ⟨π', hπ'⟩ := exists_factor φ' hφ' Rm.mkQ (by simpa using hker act' φ' hφ' e')
  refine ⟨M ⧸ Rm, inferInstance, inferInstance, actP, π, π', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨m, rfl⟩ := Rm.mkQ_surjective y
    exact ⟨φ m, hπ m⟩
  · intro y
    obtain ⟨m, rfl⟩ := Rm.mkQ_surjective y
    exact ⟨φ' m, hπ' m⟩
  · intro W x
    obtain ⟨m, rfl⟩ := hφ x
    rw [← e, hπ, hπ]
    rfl
  · intro W x
    obtain ⟨m, rfl⟩ := hφ' x
    rw [← e', hπ', hπ']
    rfl
  · exact Submodule.Quotient.nontrivial_iff.mpr hRmtop
  · intro N hN
    by_cases hc : N.comap Rm.mkQ = ⊤
    · right
      rw [eq_top_iff]
      intro y _
      obtain ⟨m, rfl⟩ := Rm.mkQ_surjective y
      have : m ∈ N.comap Rm.mkQ := hc ▸ Submodule.mem_top
      exact this
    · left
      have hst : ∀ W, ∀ x ∈ N.comap Rm.mkQ, actM W x ∈ N.comap Rm.mkQ := by
        intro W x hx
        exact hN W _ hx
      have hle : N.comap Rm.mkQ ≤ Rm := le_sSup ⟨hst, hc⟩
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨m, rfl⟩ := Rm.mkQ_surjective y
      rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hle hy
end PositivityTheory.KReal

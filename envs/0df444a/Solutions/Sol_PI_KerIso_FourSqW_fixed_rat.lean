-- Prove2me | solution 1 for PI.KerIso.FourSqW.fixed_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:47:28.074293+00:00
-- url     : https://prove2.me/submissions/7475ad78-cf0a-4764-8ade-d309cc5670ff

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_FourSqOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_OrthogonalDiagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open PI PI.KerIso PI.KerIso.FourSqW
variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
namespace PI.KerIso.FourSqW
theorem _root_.solution (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (h2 : finrank ℚ K = 2) (k : K)
    (hk : cj (algebraMap K E k) = algebraMap K E k) : ∃ r : ℚ, k = (r : K) := by
  let φ : K →ₗ[ℚ] E := (IsScalarTower.toAlgHom ℚ K E).toLinearMap
  let L : K →ₗ[ℚ] E := cj.toLinearMap.comp φ - φ
  have hL : ∀ x, L x = cj (algebraMap K E x) - algebraMap K E x := fun x => rfl
  have hker : ∀ x, x ∈ LinearMap.ker L ↔ cj (algebraMap K E x) = algebraMap K E x := by
    intro x; rw [LinearMap.mem_ker, hL, sub_eq_zero]
  have hrange : LinearMap.range L ≠ ⊥ := by
    obtain ⟨k0, hk0⟩ := hc.2.2
    intro h
    rw [LinearMap.range_eq_bot] at h
    apply hk0
    have := congrArg (fun f : K →ₗ[ℚ] E => f k0) h
    simp only [LinearMap.zero_apply, hL, sub_eq_zero] at this
    exact this
  have hr1 : 1 ≤ finrank ℚ (LinearMap.range L) := Submodule.one_le_finrank_iff.mpr hrange
  have hsum := L.finrank_range_add_finrank_ker
  have hk1 : finrank ℚ (LinearMap.ker L) ≤ 1 := by omega
  have h1mem : (1 : K) ∈ LinearMap.ker L := by
    rw [hker, map_one, map_one]
  have hle : Submodule.span ℚ {(1 : K)} ≤ LinearMap.ker L := by
    rw [Submodule.span_le, Set.singleton_subset_iff]; exact h1mem
  have hfr : finrank ℚ (Submodule.span ℚ {(1 : K)}) = 1 := finrank_span_singleton one_ne_zero
  have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
  have hkmem : k ∈ Submodule.span ℚ {(1 : K)} := by rw [heq, hker]; exact hk
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hkmem
  exact ⟨r, by rw [← hr, Rat.smul_one_eq_cast]⟩
end PI.KerIso.FourSqW

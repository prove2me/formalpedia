-- Prove2me | solution 1 for PI.LocHaarRRW.pair_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:52:34.333798+00:00
-- url     : https://prove2.me/submissions/f2a729b4-1628-4135-93cb-ac901e20bd12

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalHaarSubgroup_ExistsHaarOfSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel MeasureTheory Topology Polynomial
open PI PI.LocHaarRRW
variable {K V : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CharZero K] [CommRing V] [Algebra K V]
namespace PI.LocHaarRRW
theorem _root_.solution [Nontrivial V] {θ : V} (hθ : θ ∉ (algebraMap K V).range) (s t : K)
    (h : s • (1 : V) + t • θ = 0) : s = 0 ∧ t = 0 := by
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at h
    exact ⟨h, rfl⟩
  · exfalso
    apply hθ
    refine ⟨-(t⁻¹ * s), ?_⟩
    have h1 : t • θ = -(s • (1 : V)) := eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact h)
    have h2 : θ = t⁻¹ • (t • θ) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    rw [h2, h1, smul_neg, smul_smul, ← neg_smul, Algebra.algebraMap_eq_smul_one]
end PI.LocHaarRRW

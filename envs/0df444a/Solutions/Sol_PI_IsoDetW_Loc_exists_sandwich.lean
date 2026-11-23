-- Prove2me | solution 1 for PI.IsoDetW.Loc.exists_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:39:24.636089+00:00
-- url     : https://prove2.me/submissions/525e4c34-5903-43eb-8f9f-bf441b0a9152

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_AlgebraMapMemCI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap
import Theorems.Thm_PI_IsoDetW_Loc_exists_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoDetW PI.IsoDetW.Loc
open PI.IsoDetDefs IsDedekindDomain
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
local notation "FI" => FractionalIdeal (nonZeroDivisors R) K
namespace PI.IsoDetW.Loc
theorem _root_.solution (I : FI) (hI : I ≠ 0) :
    ∃ r : R, r ≠ 0 ∧ FractionalIdeal.spanSingleton _ (algebraMap R K r) ≤ I ∧
      I ≤ FractionalIdeal.spanSingleton _ (algebraMap R K r)⁻¹ := by
  obtain ⟨a, ha, J, hJ, hIJ⟩ := exists_integral I hI
  have ha' : algebraMap R K a ≠ 0 := by
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact ha
  obtain ⟨j, hjJ, hj0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  refine ⟨a * j, mul_ne_zero ha hj0, ?_, ?_⟩
  ·
    rw [FractionalIdeal.spanSingleton_le_iff_mem]
    have : algebraMap R K j ∈ FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K a) * I := by
      rw [hIJ]; exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨j, hjJ, rfl⟩
    obtain ⟨x, hx, hxe⟩ := (FractionalIdeal.mem_singleton_mul).mp this
    have e : algebraMap R K (a * j) = (a * a) • x := by
      rw [map_mul, hxe, Algebra.smul_def, map_mul]; ring
    rw [e]
    exact FractionalIdeal.mem_coe.mp (Submodule.smul_mem _ _ (FractionalIdeal.mem_coe.mpr hx))
  · intro x hx
    have hj' : algebraMap R K j ≠ 0 := by
      rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact hj0
    have hax : algebraMap R K a * x ∈ (J : FI) := by
      rw [← hIJ]; exact FractionalIdeal.mem_singleton_mul.mpr ⟨x, hx, rfl⟩
    obtain ⟨z, -, hze⟩ := (FractionalIdeal.mem_coeIdeal _).mp hax
    rw [FractionalIdeal.mem_spanSingleton]
    refine ⟨j * z, ?_⟩
    rw [Algebra.smul_def, map_mul, map_mul, hze]
    field_simp
end PI.IsoDetW.Loc

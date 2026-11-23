-- Prove2me | solution 1 for PI.IsoDetW.Loc.exists_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:34:25.810968+00:00
-- url     : https://prove2.me/submissions/3f73d96a-e5b2-4096-8681-652d9d9977da

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_AlgebraMapMemCI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap

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
    ∃ a : R, a ≠ 0 ∧ ∃ J : Ideal R, J ≠ 0 ∧
      FractionalIdeal.spanSingleton _ (algebraMap R K a) * I = (J : FI) := by
  obtain ⟨a, J, ha, hIJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have ha' : algebraMap R K a ≠ 0 := by
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact ha
  refine ⟨a, ha, J, ?_, ?_⟩
  · rintro rfl
    apply hI
    rw [hIJ]; simp
  · rw [hIJ, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv_cancel₀ ha',
      FractionalIdeal.spanSingleton_one, one_mul]
end PI.IsoDetW.Loc

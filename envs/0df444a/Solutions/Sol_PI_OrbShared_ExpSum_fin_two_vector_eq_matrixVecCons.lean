-- Prove2me | solution 1 for PI.OrbShared.ExpSum.fin_two_vector_eq_matrixVecCons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:27.595586+00:00
-- url     : https://prove2.me/submissions/c90f74c0-d4f2-48f9-8a9c-104f0646d819

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_ExpSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.OrbShared PI.OrbShared.ExpSum
open MvPowerSeries
variable {K : Type*} [Field K] [CharZero K]
namespace PI.OrbShared.ExpSum
theorem _root_.solution (e : Fin 2 →₀ ℕ) (k j : ℕ) :
    e = Finsupp.single 0 k + Finsupp.single 1 j ↔ e 0 = k ∧ e 1 = j := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i <;> simp [h0, h1]
end PI.OrbShared.ExpSum

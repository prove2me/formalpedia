-- Prove2me | solution 1 for PI.DensSplitW.phiX_finrank_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:13.816037+00:00
-- url     : https://prove2.me/submissions/5144fca2-f64e-4c8b-9a6e-49e43d7f8aec

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_FiberCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_PhiXFinrankRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.L2.SG.DensExact
open PI PI.DensSplitW
namespace PI.DensSplitW
theorem _root_.solution {K : Type} [Field K] {n m : ℕ} (Ph : Matrix (Fin n) (Fin n) K)
    (hPh : IsUnit Ph.det) (X : Fin m → Fin n → K) (hX : LinearIndependent K X) :
    Module.finrank K (LinearMap.range (phiX Ph X)) = m := by
  have h1 : (Matrix.of X * Ph).rank = m := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det Ph _ hPh, Matrix.rank_eq_finrank_span_row]
    exact (finrank_span_eq_card hX).trans (Fintype.card_fin m)
  exact h1
end PI.DensSplitW

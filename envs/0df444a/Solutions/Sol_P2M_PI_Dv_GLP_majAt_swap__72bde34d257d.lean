-- Prove2me | solution 1 for P2M_PI_Dv_GLP_majAt_swap__72bde34d257d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:44:06.373803+00:00
-- url     : https://prove2.me/submissions/286623db-883e-4efa-85e1-8887c08408ac

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_MajAtZeroRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Formalism.HermitianLatticesTheory NumberField
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
  (v : InfinitePlace K)
namespace PI.Dv.GLP
theorem _root_.solution (x y : V) : majAt b X v y x = star (majAt b X v x y) := by
  unfold majAt
  rw [star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_mul', star_star, mul_comm]
end PI.Dv.GLP

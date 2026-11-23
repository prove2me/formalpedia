-- Prove2me | solution 1 for P2M_PI_SqfRootsInj_W_minpoly_monic__d5b12cc188a0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:27.9378+00:00
-- url     : https://prove2.me/submissions/217290c2-4e69-4c53-82fc-6dcc15e8261a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_DivCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_TwoPowCardPrimeFactorsLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_CardLeSumOfCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Classical
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab
namespace PI.SqfRootsInj.W
theorem _root_.solution {g : ℕ} [Fact g.Prime] (w : Fbar g) : (minpoly (ZMod g) w).Monic :=
  minpoly.monic (Algebra.IsIntegral.isIntegral w)
end PI.SqfRootsInj.W

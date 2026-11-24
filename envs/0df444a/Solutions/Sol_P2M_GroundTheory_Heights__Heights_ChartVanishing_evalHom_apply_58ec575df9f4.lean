-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartVanishing_evalHom_apply_58ec575df9f4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:17.672886+00:00
-- url     : https://prove2.me/submissions/51b306c0-d4ab-46ed-af82-c8b47380baea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroTer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartVanishing
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.ChartVanishing
theorem _root_.solution {F : Type*} [CommRing F] (z : Cone n F) (f : MvPolynomial (Coord n) ℤ) :
    evalHom z f = evalCone z f := rfl
end GroundTheory.Heights₂.Heights.ChartVanishing

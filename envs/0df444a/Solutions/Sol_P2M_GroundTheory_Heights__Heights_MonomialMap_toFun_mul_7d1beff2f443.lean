-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MonomialMap_toFun_mul_7d1beff2f443
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:13:05.786771+00:00
-- url     : https://prove2.me/submissions/1f50e9cb-22a2-4aaf-9280-270edca53a3f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroAlt

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
open GroundTheory.Heights₂.Heights.MonomialMap
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {P : ArithVariety n}
namespace GroundTheory.Heights₂.Heights.MonomialMap
theorem _root_.solution {a b : ι → ℤ} (s : IntegralSection P a) (t : IntegralSection P b) :
    (s.mul t).toFun = s.toFun * t.toFun := by
  simp only [IntegralSection.toFun, IntegralSection.mul, map_mul, div_mul_div_comm]
end GroundTheory.Heights₂.Heights.MonomialMap

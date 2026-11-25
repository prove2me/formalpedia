-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MonomialMap_toFun_pow_c43df090b05d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:37:11.848892+00:00
-- url     : https://prove2.me/submissions/af25b8b8-021d-442d-b4d6-5f13676d7694

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
theorem _root_.solution {a : ι → ℤ} (s : IntegralSection P a) (m : ℕ) :
    (s.pow m).toFun = s.toFun ^ m := by
  simp only [IntegralSection.toFun, IntegralSection.pow, map_pow, div_pow]
end GroundTheory.Heights₂.Heights.MonomialMap

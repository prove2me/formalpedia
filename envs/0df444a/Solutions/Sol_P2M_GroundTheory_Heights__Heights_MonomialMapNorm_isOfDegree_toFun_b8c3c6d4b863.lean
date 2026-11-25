-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isOfDegree_toFun_b8c3c6d4b863
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:27:41.741804+00:00
-- url     : https://prove2.me/submissions/43aab52e-df8b-4dc1-8c56-3b2accfb2c8c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroBis

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
open GroundTheory.Heights₂.Heights.MonomialMapNorm
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (P : ArithVariety n)
namespace GroundTheory.Heights₂.Heights.MonomialMapNorm
theorem _root_.solution {a : ι → ℤ} (s : IntegralSection P a) : P.IsOfDegree a s.toFun :=
  ⟨s.num, s.den, s.numDeg, s.denDeg, s.num_isHomogeneous, s.den_isHomogeneous, s.deg_eq, s.den_not_mem, rfl⟩
end GroundTheory.Heights₂.Heights.MonomialMapNorm

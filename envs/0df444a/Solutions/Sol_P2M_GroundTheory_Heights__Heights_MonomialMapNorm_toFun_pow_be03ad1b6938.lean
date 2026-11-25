-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MonomialMapNorm_toFun_pow_be03ad1b6938
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:27:45.1789+00:00
-- url     : https://prove2.me/submissions/780cda64-0cfc-4067-836f-e5013c52f814

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
theorem _root_.solution {a : ι → ℤ} (s : IntegralSection P a) (m : ℕ) : (s.pow m).toFun = s.toFun ^ m := by
  simp only [IntegralSection.toFun, IntegralSection.pow, map_pow, div_pow]
end GroundTheory.Heights₂.Heights.MonomialMapNorm

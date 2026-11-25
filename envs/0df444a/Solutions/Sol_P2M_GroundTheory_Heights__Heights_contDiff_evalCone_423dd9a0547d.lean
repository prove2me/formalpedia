-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_contDiff_evalCone_423dd9a0547d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:26:23.380901+00:00
-- url     : https://prove2.me/submissions/74ecef26-0c1c-4129-852c-a718ee285128

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_MemPointsOfGeneratorsVanish

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
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (f : MvPolynomial (Coord n) ℤ) :
    ContDiff ℝ ∞ (fun z : Cone n ℂ ↦ evalCone z f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa only [evalCone, eval₂_C] using contDiff_const
  | add p q hp hq => simpa only [evalCone, eval₂_add] using hp.add hq
  | mul_X p v hp =>
    simpa only [evalCone, eval₂_mul, eval₂_X] using
      hp.mul (contDiff_pi.1 (contDiff_pi.1 contDiff_id v.1) v.2)
end GroundTheory.Heights₂.Heights

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionInjectivity_deg_eq_b9c28d0b278f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:15:22.866493+00:00
-- url     : https://prove2.me/submissions/3994fd9a-79b6-4243-b6db-054b84bdf0cc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroMore

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.SectionInjectivity
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Heights.SectionInjectivity
theorem _root_.solution (M : HermLine n) {k q : ℕ} (hkq : k < q) (t : ℕ) :
    (((M.pow (q - k)).mul (HermLine.standard n)).pow t).deg +
        t • ((M.pow k).mul (HermLine.standard n).inv).deg = (M.pow (q * t)).deg := by
  ext i
  change (t • ((q - k) • M.deg + fun _ ↦ (1 : ℤ)) : ι → ℤ) i +
      (t • (k • M.deg + -fun _ ↦ (1 : ℤ)) : ι → ℤ) i = ((q * t) • M.deg : ι → ℤ) i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, nsmul_eq_mul, Nat.cast_sub hkq.le, Nat.cast_mul,
    Pi.mul_apply, Pi.sub_apply, Pi.natCast_apply]
  ring
end GroundTheory.Heights₂.Heights.SectionInjectivity

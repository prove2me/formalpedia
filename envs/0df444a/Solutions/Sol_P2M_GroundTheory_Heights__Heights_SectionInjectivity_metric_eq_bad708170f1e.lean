-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionInjectivity_metric_eq_bad708170f1e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:15:34.475797+00:00
-- url     : https://prove2.me/submissions/558af6b3-8d02-4f7b-9878-487ab6caf585

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
theorem _root_.solution (M : HermLine n) {k q : ℕ} (hkq : k < q) (t : ℕ) {z : Cone n ℂ}
    (hz : BlockNonzero z) :
    (M.pow (q * t)).metric z = (((M.pow (q - k)).mul (HermLine.standard n)).pow t).metric z *
        ((M.pow k).mul (HermLine.standard n).inv).metric z ^ t := by
  have hH := ((HermLine.standard n).metric_pos z hz).ne'
  simp only [HermLine.pow, HermLine.mul, HermLine.inv]
  rw [← mul_pow, pow_mul]
  congr 1
  have hq : M.metric z ^ q = M.metric z ^ (q - k) * M.metric z ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hkq.le]
  rw [hq]
  field_simp
end GroundTheory.Heights₂.Heights.SectionInjectivity

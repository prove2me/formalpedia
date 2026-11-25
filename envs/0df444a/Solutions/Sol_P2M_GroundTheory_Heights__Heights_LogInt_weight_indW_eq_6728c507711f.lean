-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_weight_indW_eq_6728c507711f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:03:39.628179+00:00
-- url     : https://prove2.me/submissions/af575165-7741-47f2-9f27-db3cdc9a97a3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_weight_indW_615073ae8b8c

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
open MeasureTheory Set MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {ι : Type*}
namespace GroundTheory.Heights₂.Heights.LogInt
theorem _root_.solution (x : ι) [DecidableEq ι] (m : ι →₀ ℕ) :
    Finsupp.weight (indW (· = x)) m = m x := by
  rw [weight_indW, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.mp h).symm
end GroundTheory.Heights₂.Heights.LogInt

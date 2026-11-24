-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_inh_fib_eq_3eb15ec2cff6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:00.443878+00:00
-- url     : https://prove2.me/submissions/d290fd2d-97b4-474b-9acc-cd71ad460ff8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants

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
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial
noncomputable section
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution : fibreClass 1 1 1 .last = 1 := by
  simp [fibreClass, vandermondeOf]
end GroundTheory.Heights₂.Heights.RestTerms

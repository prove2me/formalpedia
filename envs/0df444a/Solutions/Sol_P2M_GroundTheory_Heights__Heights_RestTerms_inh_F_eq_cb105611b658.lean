-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_inh_F_eq_cb105611b658
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:47.991666+00:00
-- url     : https://prove2.me/submissions/e7583357-3466-4626-bcb2-6fc7613e6349

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_inh_mu_eq_f35e2c531be1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_inh_fib_eq_3eb15ec2cff6

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
theorem _root_.solution : restPolynomial 1 1 1 .last = flagTwoSecondRoot ^ 2 := by
  simp [restPolynomial, inh_mu_eq, inh_fib_eq]
end GroundTheory.Heights₂.Heights.RestTerms

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_VertTermEq_proof_84fc7ba4561c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:53:59.327837+00:00
-- url     : https://prove2.me/submissions/43cf7439-adf6-44c2-98ea-e9ef3b2e7c62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PVertTermEq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_vertComps_finite_caa4eaa24ca7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
namespace VertTermEq
theorem _root_.solution : VertTermEq.Statement := by
  intro K _ _ n e I u v
  have hfin := vertComps_finite I u v
  unfold vertTermAt vertDeg
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun W _ => ?_
  push_cast
  ring
end VertTermEq
end GroundTheory.Heights₂.Heights.Vertical

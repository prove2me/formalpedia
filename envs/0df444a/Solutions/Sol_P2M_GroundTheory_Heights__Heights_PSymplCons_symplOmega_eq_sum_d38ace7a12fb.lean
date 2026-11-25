-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplCons_symplOmega_eq_sum_d38ace7a12fb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:18.674228+00:00
-- url     : https://prove2.me/submissions/e6d72e81-e6eb-4779-9892-324a14ba9edc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplCons
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplCons_J_mulVec_inl_c1577ead8cc0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplCons_J_mulVec_inr_75697f95e740

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
open Matrix
open GroundTheory.Heights₂.Heights.PSymplCons
namespace GroundTheory.Heights₂.Heights.PSymplCons
theorem _root_.solution {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (u v : l ⊕ l → R) :
    symplOmega u v = ∑ i, (u (Sum.inr i) * v (Sum.inl i) - u (Sum.inl i) * v (Sum.inr i)) := by
  unfold symplOmega dotProduct
  rw [Fintype.sum_sum_type]
  simp only [J_mulVec_inl, J_mulVec_inr, mul_neg, Finset.sum_neg_distrib]
  rw [Finset.sum_sub_distrib]
  ring
end GroundTheory.Heights₂.Heights.PSymplCons

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_blockVandermonde_ne_zero_90c17aff8bcb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:12:04.196714+00:00
-- url     : https://prove2.me/submissions/ee62cbff-3e71-4e9e-80ec-e147d88cb394

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltPush
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PLemmaB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution (f N : ℕ) : blockVandermonde f N ≠ 0 := by
  unfold blockVandermonde vandermondeOf
  refine Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun i _ =>
    Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr ?_
  intro h
  have h' := X_injective h
  simp only [Prod.mk.injEq, true_and] at h'
  exact (ne_of_lt (Finset.mem_Ioi.mp hj)) h'
end GroundTheory.Heights₂.Heights.RestTerms

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagVandermondeDvd_blockVandermonde_eq_prod_643e36086d8c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:51:57.715532+00:00
-- url     : https://prove2.me/submissions/bdfec160-fcbc-4448-b3f6-9500fe2e53c0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagVandermondeDvd

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
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.FlagVandermondeDvd
namespace GroundTheory.Heights₂.Heights.RestTerms.FlagVandermondeDvd
theorem _root_.solution (f N : ℕ) :
    blockVandermonde f N =
      ∏ t ∈ (univ : Finset (Fin f × Fin N × Fin N)).filter (fun t => t.2.1 < t.2.2),
        ((X (t.1, t.2.1) - X (t.1, t.2.2) : RootRing f N)) := by
  rw [Finset.prod_filter, Fintype.prod_prod_type]
  simp only [blockVandermonde, vandermondeOf]
  refine Finset.prod_congr rfl (fun τ _ => ?_)
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have : Finset.Ioi i = (univ : Finset (Fin N)).filter (fun j => i < j) := by ext; simp
  rw [this, Finset.prod_filter]
end GroundTheory.Heights₂.Heights.RestTerms.FlagVandermondeDvd

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockVandermonde_ne_zero_016099f0580e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:47.23963+00:00
-- url     : https://prove2.me/submissions/30b80f87-3164-4608-9b88-fb9f37b2c413

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_vandermondeOf_X_ne_zero_c074763c9980

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
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution (f N : ℕ) : blockVandermonde f N ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun τ _ => vandermondeOf_X_ne_zero f N τ
end GroundTheory.Heights₂.Heights.RestTerms.Top

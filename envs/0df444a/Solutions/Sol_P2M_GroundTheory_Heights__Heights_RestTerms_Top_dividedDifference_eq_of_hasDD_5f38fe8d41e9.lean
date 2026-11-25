-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_dividedDifference_eq_of_hasDD_5f38fe8d41e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:55:30.42871+00:00
-- url     : https://prove2.me/submissions/64e7cab3-d338-4fb6-9ca3-f5300b9be398

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockVandermonde_ne_zero_016099f0580e

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
theorem _root_.solution {f N : ℕ} {H P : RootRing f N} (h : HasDD f N H P) :
    dividedDifference f N H = algebraMap (RootRing f N) (FractionRing (RootRing f N)) P := by
  have hV : algebraMap (RootRing f N) (FractionRing (RootRing f N)) (blockVandermonde f N) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (blockVandermonde_ne_zero f N)
  rw [dividedDifference, h, map_mul, mul_div_cancel_left₀ _ hV]
end GroundTheory.Heights₂.Heights.RestTerms.Top

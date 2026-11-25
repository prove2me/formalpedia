-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_of_dividedDifference_eq_219f21cc1918
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:30:45.598238+00:00
-- url     : https://prove2.me/submissions/70c14162-b40d-4537-8a20-62fc228d98d9

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
theorem _root_.solution {f N : ℕ} {H P : RootRing f N}
    (h : dividedDifference f N H = algebraMap (RootRing f N) (FractionRing (RootRing f N)) P) :
    HasDD f N H P := by
  have hV : algebraMap (RootRing f N) (FractionRing (RootRing f N)) (blockVandermonde f N) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (blockVandermonde_ne_zero f N)
  rw [dividedDifference, div_eq_iff hV, ← map_mul] at h
  exact IsFractionRing.injective _ _ (by rw [h, mul_comm])
end GroundTheory.Heights₂.Heights.RestTerms.Top

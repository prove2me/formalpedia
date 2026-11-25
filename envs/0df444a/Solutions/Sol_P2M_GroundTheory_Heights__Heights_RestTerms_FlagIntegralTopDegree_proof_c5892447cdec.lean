-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagIntegralTopDegree_proof_c5892447cdec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:14:29.438622+00:00
-- url     : https://prove2.me/submissions/14a4c20f-3a78-4b2d-a1b3-a13500c3743c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagIntegralTopDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockVandermonde_ne_zero_737fbd71d1a2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_isBlockAlternating_antisymmetrize_1230b0a0ab9c


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
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FlagIntegralTopDegree
theorem _root_.solution (h1 : FlagAltTopDegree.Statement)
    (h2 : FlagAntisymHomogeneous.Statement) (h3 : FlagIntegralViaQuotient.Statement) :
    FlagIntegralTopDegree.Statement := by
  intro f N H hH
  obtain ⟨e, he⟩ := h1 f N (antisymmetrize f N H) (isBlockAlternating_antisymmetrize f N H)
    (h2 f N H _ hH)
  have hI := h3 f N H (C e) (by rw [he, mul_comm])
  rw [constantCoeff_C] at hI
  have hΔ : algebraMap (RootRing f N) (FractionRing (RootRing f N)) (blockVandermonde f N) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (RootRing f N) (FractionRing (RootRing f N)))).mpr
      (Flag.blockVandermonde_ne_zero f N)
  have hdd : dividedDifference f N H = algebraMap ℚ (FractionRing (RootRing f N)) e := by
    rw [dividedDifference, he, map_mul, mul_div_assoc, div_self hΔ, mul_one,
      IsScalarTower.algebraMap_apply ℚ (RootRing f N) (FractionRing (RootRing f N)),
      MvPolynomial.algebraMap_eq]
  rw [hdd, ← map_mul, hI]
end FlagIntegralTopDegree
end GroundTheory.Heights₂.Heights.RestTerms

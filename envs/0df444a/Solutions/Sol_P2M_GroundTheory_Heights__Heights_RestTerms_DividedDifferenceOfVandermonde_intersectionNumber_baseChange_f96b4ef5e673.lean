-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_DividedDifferenceOfVandermonde_intersectionNumber_baseChange_f96b4ef5e673
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:35:59.440653+00:00
-- url     : https://prove2.me/submissions/e70e2a00-0aaa-4de1-8ba3-0ed734dd057a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockVandermonde_ne_zero_737fbd71d1a2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_antisymmetrize_blockVandermonde_e253c2e15948

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
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace DividedDifferenceOfVandermonde
theorem _root_.solution : DividedDifferenceOfVandermonde.Statement := by
  intro f N
  rw [dividedDifference, Flag.antisymmetrize_blockVandermonde, Algebra.smul_def, map_mul,
    mul_div_assoc, div_self, mul_one]
  · exact (IsScalarTower.algebraMap_apply ℚ (RootRing f N) _ _).symm
  · intro h
    exact Flag.blockVandermonde_ne_zero f N
      ((IsFractionRing.injective (RootRing f N) (FractionRing (RootRing f N))) (by simpa using h))
end DividedDifferenceOfVandermonde
end GroundTheory.Heights₂.Heights.RestTerms

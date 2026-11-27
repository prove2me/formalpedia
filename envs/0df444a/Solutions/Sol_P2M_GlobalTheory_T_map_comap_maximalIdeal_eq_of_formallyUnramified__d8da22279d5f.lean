-- Prove2me | solution 1 for P2M_GlobalTheory_T_map_comap_maximalIdeal_eq_of_formallyUnramified__d8da22279d5f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:53:14.505277+00:00
-- url     : https://prove2.me/submissions/4a1523a3-fc29-405d-9c72-88ed0cbbee3e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapComapMaximalIdealEqOfFormallyUnramified
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapComapMaximalIdealEqOfFormallyUnramifiedStatement
import Theorems.Thm_GlobalTheory_map_comap_maximalIdeal_eq_of_formallyUnramified


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A B : Type) [CommRing A] [CommRing B] [IsLocalRing B] [Algebra A B] [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B], ((IsLocalRing.maximalIdeal B).comap (algebraMap A B)).map (algebraMap A B) = IsLocalRing.maximalIdeal B := by
  first | exact @GlobalTheory.map_comap_maximalIdeal_eq_of_formallyUnramified | exact GlobalTheory.map_comap_maximalIdeal_eq_of_formallyUnramified | (intros; apply GlobalTheory.map_comap_maximalIdeal_eq_of_formallyUnramified <;> assumption)
end _root_.GlobalTheory.T

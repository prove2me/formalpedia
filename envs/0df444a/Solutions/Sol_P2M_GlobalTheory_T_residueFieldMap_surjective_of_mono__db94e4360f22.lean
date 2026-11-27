-- Prove2me | solution 1 for P2M_GlobalTheory_T_residueFieldMap_surjective_of_mono__db94e4360f22
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:53:20.016122+00:00
-- url     : https://prove2.me/submissions/4a585c6f-4b6d-43f2-ae45-9e1794667fe3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueFieldMapSurjectiveOfMono
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueFieldMapSurjectiveOfMonoStatement
import Theorems.Thm_GlobalTheory_residueFieldMap_surjective_of_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [Mono f] (x : X), Function.Surjective (f.residueFieldMap x).hom := by
  first | exact @GlobalTheory.residueFieldMap_surjective_of_mono | exact GlobalTheory.residueFieldMap_surjective_of_mono | (intros; apply GlobalTheory.residueFieldMap_surjective_of_mono <;> assumption)
end _root_.GlobalTheory.T

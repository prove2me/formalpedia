-- Prove2me | solution 1 for P2M_GlobalTheory_T_faithfullyFlat_app_of_isAffineHom_flat_surjective__ca00d372e8df
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:53:29.130843+00:00
-- url     : https://prove2.me/submissions/4d602389-0a42-46a9-bc1a-f305f754b832

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FaithfullyFlatAppOfIsAffineHomFlatSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FaithfullyFlatAppOfIsAffineHomFlatSurjectiveStatement
import Theorems.Thm_GlobalTheory_faithfullyFlat_app_of_isAffineHom_flat_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (V : Y.Opens), IsAffineHom p → Flat p → Surjective p → IsAffineOpen V → (p.app V).hom.FaithfullyFlat := by
  first | exact @GlobalTheory.faithfullyFlat_app_of_isAffineHom_flat_surjective | exact GlobalTheory.faithfullyFlat_app_of_isAffineHom_flat_surjective | (intros; apply GlobalTheory.faithfullyFlat_app_of_isAffineHom_flat_surjective <;> assumption)
end _root_.GlobalTheory.T

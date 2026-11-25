-- Prove2me | solution 1 for P2M_GlobalTheory_T_isDominant_homOfVector_of_quasiFiniteAt__199183cd97e7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:33:40.876912+00:00
-- url     : https://prove2.me/submissions/c8fb41ff-81ac-4798-bf8f-d7beea89f71e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsDominantHomOfVectorOfQuasiFiniteAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsDominantHomOfVectorOfQuasiFiniteAtStatement
import Theorems.Thm_GlobalTheory_isDominant_homOfVector_of_quasiFiniteAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X Z : Scheme.{0}) [IsIntegral X] [IsIntegral Z] (t : X ⟶ Z) [LocallyOfFiniteType t] (g : ℕ) (U : X.Opens), (U : Set X).Nonempty → SmoothOfRelativeDimension g (U.ι ≫ t) → ∀ (u : Fin g → Γ(X, ⊤)) (w : X), (AffineSpace.homOfVector t u).QuasiFiniteAt w → IsDominant (AffineSpace.homOfVector t u) := by
  first | exact @GlobalTheory.isDominant_homOfVector_of_quasiFiniteAt | exact GlobalTheory.isDominant_homOfVector_of_quasiFiniteAt | (intros; apply GlobalTheory.isDominant_homOfVector_of_quasiFiniteAt <;> assumption)
end _root_.GlobalTheory.T

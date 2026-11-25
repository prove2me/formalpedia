-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_classical_lift_of_smooth__40cd1848fc21
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:34:06.868964+00:00
-- url     : https://prove2.me/submissions/2f1daf19-d760-49af-9567-c1d8e63df3b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsClassicalLiftOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsClassicalLiftOfSmoothStatement
import Theorems.Thm_GlobalTheory_ZJ_exists_classical_lift_of_smooth


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
open GlobalTheory.ZJ
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (X S : Scheme.{0}) (f : X ⟶ S) [Smooth f] (y : Sp (OO p) ⟶ S) (x : Sp (kb p) ⟶ X), x ≫ f = rPt p ≫ y → ∃ b : Sp (OO p) ⟶ X, b ≫ f = y ∧ rPt p ≫ b = x := by
  first | exact @GlobalTheory.ZJ.exists_classical_lift_of_smooth | exact GlobalTheory.ZJ.exists_classical_lift_of_smooth | (intros; apply GlobalTheory.ZJ.exists_classical_lift_of_smooth <;> assumption)
end _root_.GlobalTheory.T

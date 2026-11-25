-- Prove2me | solution 1 for P2M_GlobalTheory_ZM_RepBC_le__8683792fd0d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:10:17.050824+00:00
-- url     : https://prove2.me/submissions/3d9073d0-d098-4543-a5e4-a553399d43b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ProjectiveRepresentationPullbackCoordinates
import Theorems.Thm_GlobalTheory_ZM_RepBC_le_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.RepBC
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.ZM.RepBC
theorem _root_.solution (M : LB X) (π : Y ⟶ X) (x : Z ⟶ Y) (j : PUnit → M.ι) :
    (M.pull (x ≫ π)).U j ≤ ((M.pull π).pull x).U (fun _ => j) :=
  fun _ h => le_pull (M.pull π) x (fun _ => j) (le_pull M π _ (pull_le M (x ≫ π) j h))
end GlobalTheory.ZM.RepBC

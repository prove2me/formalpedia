-- Prove2me | solution 1 for P2M_GlobalTheory_valAt__constFn_1b31686fad50
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:03.588728+00:00
-- url     : https://prove2.me/submissions/d3fcdf26-7f35-4255-9ed2-8d8fead23748

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Theorems.Thm_P2M_GlobalTheory_valAt__appLE_1af07a5a9e22
import Theorems.Thm_P2M_GlobalTheory_valAt__id_top_2b98de8ae8d0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
variable {X Y : Scheme.{0}}
namespace GlobalTheory
theorem _root_.solution (x : Sp ℂ ⟶ X) (p : X ⟶ Sp ℂ) (hp : x ≫ p = 𝟙 _) (U : X.Opens) (a : ℂ)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : valAt' x U (constFn p U a) = a := by
  refine (valAt'_appLE x p ⊤ U le_top _ h).trans ?_
  rw [hp, valAt'_id_top]
end GlobalTheory

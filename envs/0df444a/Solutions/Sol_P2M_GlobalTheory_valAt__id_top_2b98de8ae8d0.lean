-- Prove2me | solution 1 for P2M_GlobalTheory_valAt__id_top_2b98de8ae8d0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:03.991445+00:00
-- url     : https://prove2.me/submissions/736323b9-7a6e-4f52-9d84-95d1d7ef7a12

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Theorems.Thm_P2M_GlobalTheory_valAt__eq_valAt_cd16e0b92c48

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
theorem _root_.solution (a : ℂ) :
    valAt' (𝟙 (Sp ℂ)) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a) = a := by
  rw [valAt'_eq_valAt (𝟙 (Sp ℂ)) (U := ⊤) le_top]
  unfold valAt
  simp [Scheme.Hom.appLE]
end GlobalTheory

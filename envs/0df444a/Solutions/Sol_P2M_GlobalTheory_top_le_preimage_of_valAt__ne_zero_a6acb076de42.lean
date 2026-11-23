-- Prove2me | solution 1 for P2M_GlobalTheory_top_le_preimage_of_valAt__ne_zero_a6acb076de42
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:07:20.070865+00:00
-- url     : https://prove2.me/submissions/f5ec7319-b54a-4d36-85b9-0b0a45f8ff6d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Theorems.Thm_P2M_GlobalTheory_valAt__of_not_le_8b0812974c03

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
theorem _root_.solution (x : Sp ℂ ⟶ X) {U : X.Opens} {f : Γ(X, U)} (h : valAt' x U f ≠ 0) :
    ⊤ ≤ x ⁻¹ᵁ U := by
  by_contra hU
  exact h (valAt'_of_not_le x hU f)
end GlobalTheory

-- Prove2me | solution 1 for P2M_GlobalTheory_valAt__units_zpow_e1282b23a243
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:02.035274+00:00
-- url     : https://prove2.me/submissions/f89116a9-c922-4e3c-9bd6-7fa8cde989b1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Theorems.Thm_P2M_GlobalTheory_valAt__eq_valAtHom_eb5802171cfc

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
theorem _root_.solution (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (u : Γ(X, U)ˣ) (n : ℤ) :
    valAt' x U (u ^ n).val = valAt' x U u.val ^ n := by
  simp only [valAt'_eq_valAtHom x h]
  have := congrArg Units.val (map_zpow (Units.map (valAtHom x U h : Γ(X, U) →* ℂ)) u n)
  rw [Units.val_zpow_eq_zpow_val] at this
  exact this
end GlobalTheory

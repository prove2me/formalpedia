-- Prove2me | solution 1 for P2M_GlobalTheory_valAt__isUnit_ne_zero_6b94376a2f54
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:33:50.240331+00:00
-- url     : https://prove2.me/submissions/83915c9b-7db1-4540-b1f5-3647f399427c

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
theorem _root_.solution (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) {f : Γ(X, U)} (hf : IsUnit f) :
    valAt' x U f ≠ 0 := by
  rw [valAt'_eq_valAtHom x h]
  exact (hf.map _).ne_zero
end GlobalTheory

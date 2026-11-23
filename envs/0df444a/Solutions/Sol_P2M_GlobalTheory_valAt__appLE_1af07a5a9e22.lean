-- Prove2me | solution 1 for P2M_GlobalTheory_valAt__appLE_1af07a5a9e22
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:19.127815+00:00
-- url     : https://prove2.me/submissions/b0f58413-4082-4266-b08d-cd26754593b1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Theorems.Thm_GlobalTheory_top_le_preimage_mono
import Theorems.Thm_GlobalTheory_top_le_preimage_comp
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
theorem _root_.solution (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (e : V ≤ φ ⁻¹ᵁ U) (f : Γ(Y, U))
    (hV : ⊤ ≤ x ⁻¹ᵁ V) : valAt' x V ((φ.appLE U V e).hom f) = valAt' (x ≫ φ) U f := by
  have hU : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := (top_le_preimage_comp x φ U).2 (top_le_preimage_mono x e hV)
  rw [valAt'_eq_valAt x hV, valAt'_eq_valAt _ hU, valAt, valAt, ← CommRingCat.comp_apply (φ.appLE U V e),
    Scheme.Hom.appLE_comp_appLE]
end GlobalTheory

-- Prove2me | solution 1 for P2M_GlobalTheory_valAt__map_238ef0722272
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:28.691807+00:00
-- url     : https://prove2.me/submissions/617e6c61-2a77-4e91-9bd8-26138478777f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Theorems.Thm_GlobalTheory_top_le_preimage_mono
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
theorem _root_.solution (x : Sp ℂ ⟶ X) {U V : X.Opens} (i : Opposite.op U ⟶ Opposite.op V) (f : Γ(X, U))
    (hV : ⊤ ≤ x ⁻¹ᵁ V) : valAt' x V ((X.presheaf.map i).hom f) = valAt' x U f := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := top_le_preimage_mono x i.unop.le hV
  rw [valAt'_eq_valAt x hV, valAt'_eq_valAt _ hU, valAt, valAt, ← CommRingCat.comp_apply (X.presheaf.map i),
    Scheme.Hom.map_appLE]
end GlobalTheory

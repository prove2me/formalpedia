-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_refl__cb32e03a41c1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:48.933993+00:00
-- url     : https://prove2.me/submissions/48c2f1ef-36d9-439c-a73c-935bc6a3e8ee

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped Classical
variable {X Y : Scheme.{0}} (L : LB X)
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {Z : Scheme.{0}} {U : Z.Opens} (x : Γ(Z, U)ˣ) : res (le_refl U) x = x := by
  ext
  show (Z.presheaf.map (𝟙 (op U))).hom x.val = x.val
  rw [CategoryTheory.Functor.map_id]
  rfl
end ReciprocityTheory.ChartRestriction.G.DVR

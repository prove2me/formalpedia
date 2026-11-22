-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_res__b0a8af1c3378
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:44:09.190096+00:00
-- url     : https://prove2.me/submissions/ec770b72-2a18-4e6a-9d85-e4ecbca51a7c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal

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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {X : Scheme.{0}} {U W Z : X.Opens} (h : W ≤ U) (h' : Z ≤ W) (x : Γ(X, U)ˣ) :
    res h' (res h x) = res (h'.trans h) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [show (homOfLE (h'.trans h)).op = (homOfLE h).op ≫ (homOfLE h').op from rfl,
    Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply]
end ReciprocityTheory.ChartRestriction.G.DVR

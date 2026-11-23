-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.res_pullU_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:48.298367+00:00
-- url     : https://prove2.me/submissions/c0bc92a5-035c-4e4f-ba36-82bd79351cb6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_res__b0a8af1c3378
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullU_res

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
theorem _root_.solution {X Y : Scheme.{0}} (f : Y ⟶ X) {U W : X.Opens} (h : W ≤ U) {Z : Y.Opens}
    (hZ : Z ≤ f ⁻¹ᵁ U) (hZ' : Z ≤ f ⁻¹ᵁ W) (x : Γ(X, U)ˣ) :
    res hZ (pullU f U x) = res hZ' (pullU f W (res h x)) := by
  rw [pullU_res, res_res']
end ReciprocityTheory.ChartRestriction.G.DVR

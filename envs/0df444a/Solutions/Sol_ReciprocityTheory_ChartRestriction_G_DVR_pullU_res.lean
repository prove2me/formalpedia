-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.pullU_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:06:51.223863+00:00
-- url     : https://prove2.me/submissions/b523f5fe-825c-42aa-a9ac-8236b24be6fa

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
theorem _root_.solution {X Y : Scheme.{0}} (f : Y ⟶ X) {U W : X.Opens} (h : W ≤ U) (x : Γ(X, U)ˣ) :
    pullU f W (res h x) = res ((TopologicalSpace.Opens.map f.base).monotone h) (pullU f U x) := by
  ext
  simp only [pullU, res, Units.coe_map, MonoidHom.coe_coe]
  have e := congrArg (fun φ => φ.hom (x : Γ(X, U))) (f.naturality (homOfLE h).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e
end ReciprocityTheory.ChartRestriction.G.DVR

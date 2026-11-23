-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.linComb_cover
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:18.16865+00:00
-- url     : https://prove2.me/submissions/2c5a67f6-d9f8-4f1c-a85d-d7b2b0ecf3fc

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
variable {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
include hL
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution : ⨆ j, (LB.LinComb L φ ε).U j = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hc : ∀ k, ∃ i, (φ k).base y ∈ L.U i := by
    intro k
    have h1 : (φ k).base y ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp h1
  choose j hj using hc
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨j, Set.mem_iInter.mpr hj⟩
end ReciprocityTheory.ChartRestriction.G.DVR

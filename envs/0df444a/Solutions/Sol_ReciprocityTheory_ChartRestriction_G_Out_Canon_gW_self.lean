-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.Canon.gW_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:21.673122+00:00
-- url     : https://prove2.me/submissions/3af1ec3a-8607-4fc4-9a29-7663d509927b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_CanonGenIsGen

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out.Canon
variable {X Y : Scheme.{0}} (L : LB X)
variable {L}
namespace ReciprocityTheory.ChartRestriction.G.Out.Canon
theorem _root_.solution (hL : L.IsLB) {W : Y.Opens} (ψ : Y ⟶ X) (a : L.ι)
    (h : W ≤ ψ ⁻¹ᵁ (L.U a ⊓ L.U a)) : gW L ψ a a h = 1 := by
  unfold gW
  rw [res_pullU_eq ψ (le_inf le_rfl le_rfl : L.U a ≤ L.U a ⊓ L.U a) h
    (h.trans (ψ.preimage_mono inf_le_left)), hL.g_self, map_one, map_one]
end ReciprocityTheory.ChartRestriction.G.Out.Canon

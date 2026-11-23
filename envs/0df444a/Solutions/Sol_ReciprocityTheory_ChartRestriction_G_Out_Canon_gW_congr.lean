-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.Canon.gW_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:21.583067+00:00
-- url     : https://prove2.me/submissions/2fa2e6e1-6053-4f6c-b20a-c871c3e66e98

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
theorem _root_.solution {W : Y.Opens} {ψ ψ' : Y ⟶ X} {a a' b b' : L.ι} (hψ : ψ = ψ') (ha : a = a')
    (hb : b = b') (h : W ≤ ψ ⁻¹ᵁ (L.U a ⊓ L.U b)) (h' : W ≤ ψ' ⁻¹ᵁ (L.U a' ⊓ L.U b')) :
    gW L ψ a b h = gW L ψ' a' b' h' := by
  subst hψ ha hb; rfl
end ReciprocityTheory.ChartRestriction.G.Out.Canon

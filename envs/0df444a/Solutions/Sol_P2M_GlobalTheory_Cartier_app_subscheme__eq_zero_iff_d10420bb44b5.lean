-- Prove2me | solution 1 for P2M_GlobalTheory_Cartier_app_subscheme__eq_zero_iff_d10420bb44b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:50:11.599269+00:00
-- url     : https://prove2.me/submissions/e4217efc-04b1-4f67-aa96-53c740ec18c8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Theorems.Thm_GlobalTheory_Cartier_ext_germ

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
open GlobalTheory GlobalTheory.Cartier
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.Cartier
theorem _root_.solution (J : Y.IdealSheafData) {V : Y.Opens} (b : Γ(Y, V)) :
    (J.subschemeι.app V).hom b = 0 ↔
      ∀ (W : Y.affineOpens) (h : W.1 ≤ V), resG Y h b ∈ J.ideal W := by
  have hk : ∀ W : Y.affineOpens, J.ideal W = RingHom.ker (J.subschemeι.app W.1).hom := fun W => by
    rw [← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]
  constructor
  · intro hb W h
    rw [hk, RingHom.mem_ker, app_resG, hb, map_zero]
  · intro h
    refine ext_germ fun z hz => ?_
    obtain ⟨_, ⟨W, hW, rfl⟩, hzW, hWV⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (a := J.subschemeι z) hz V.isOpen
    have hWV' : W ≤ V := hWV
    have := h ⟨W, hW⟩ hWV'
    rw [hk, RingHom.mem_ker, app_resG] at this
    rw [← germ_resG (J.subschemeι.preimage_mono hWV') z hzW, this, map_zero, map_zero]
end GlobalTheory.Cartier

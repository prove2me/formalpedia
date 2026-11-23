-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.linComb_g_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:14.441738+00:00
-- url     : https://prove2.me/submissions/b21fb336-0059-412c-b487-7486e3db0d65

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_def
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_res__b0a8af1c3378


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
theorem _root_.solution {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j j₂ : K → L.ι) {V : Y.Opens}
    (h : V ≤ LB.wchart L φ j ⊓ LB.wchart L φ j₂) :
    res h ((LB.LinComb L φ ε).g j j₂) = ∏ k, tr L V (φ k) (j k) (j₂ k) ^ ε k := by
  simp only [LB.LinComb]
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hk : V ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j₂ k)) := fun y hy =>
    ⟨LB.wchart_le L φ j k (h hy).1, LB.wchart_le L φ j₂ k (h hy).2⟩
  rw [map_zpow, tr_def L hk]
  erw [res_res']
  rfl
end ReciprocityTheory.ChartRestriction.G.DVR

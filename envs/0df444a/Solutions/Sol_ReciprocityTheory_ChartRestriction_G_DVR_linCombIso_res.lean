-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.linCombIso_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:51:05.298796+00:00
-- url     : https://prove2.me/submissions/24a35b3e-e609-4926-9ee5-42081cbf9a41

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tu_def

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
variable {X Y : Scheme.{0}} {L M : LB X}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (w : LB.Iso L M) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (p : (LB.LinComb M φ ε).ι × (LB.LinComb L φ ε).ι) {V : Y.Opens}
    (h : V ≤ (LB.div (LB.LinComb M φ ε) (LB.LinComb L φ ε)).U p) :
    res h ((LB.linCombIso w φ ε).s p) = ∏ k, wu w V (φ k) (p.1 k) (p.2 k) ^ ε k := by
  refine (map_prod (res h) _ Finset.univ).trans (Finset.prod_congr rfl (fun k _ => ?_))
  refine (map_zpow (res h) _ (ε k)).trans ?_
  congr 1
  have c : V ≤ φ k ⁻¹ᵁ (LB.div M L).U (p.1 k, p.2 k) :=
    h.trans (le_inf (inf_le_left.trans (LB.wchart_le M φ p.1 k))
      (inf_le_right.trans (LB.wchart_le L φ p.2 k)))
  refine (res_res_eq_res_trans' _ _ _).trans ?_
  exact (tu_def (U := (LB.div M L).U) (u := w.s) c).symm
end ReciprocityTheory.ChartRestriction.G.DVR

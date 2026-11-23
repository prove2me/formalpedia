-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.box_sec_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:48:15.049795+00:00
-- url     : https://prove2.me/submissions/ae6f45c4-0c2d-4aac-9329-db4396864062

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gs_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gm_linCombIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X X' Y Z : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K] {φ' : K → (X' ⟶ X')}
    {φ : Fin j → K → (X ⟶ X)} {ε : K → ℤ} (hφ : ∀ i a, φ' a ≫ pr i = pr i ≫ φ i a) (s' : LB.Sec (LB.LinComb M' φ' ε))
    (s : ∀ i, LB.Sec (LB.LinComb M (φ i) ε))
    (hle : ∀ (jN : K → Fin j → M.ι) (jM : K → M'.ι) i, LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM ≤
      pr i ⁻¹ᵁ LB.wchart M (φ i) (fun a => jN a i))
    (H : ∀ (jN : K → Fin j → M.ι) (jM : K → M'.ι),
      (@id (Γ(X', LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM)ˣ)
        ((LB.linCombIso w φ' ε).s (jN, jM))).val * rs inf_le_right (s'.f jM) =
        ∏ i, rs (hle jN jM i) (((pr i).app _).hom ((s i).f (fun a => jN a i))))
    (q : Z ⟶ X') (y : Z) {J J'} (hJ : Good M y J) (hJ' : Good M' y J') :
    (∏ a, bw w (q ≫ φ' a) y (fun i => J ((q ≫ φ' a) ≫ pr i)) (J' (q ≫ φ' a)) ^ ε a).val * sval s' q y J' =
      ∏ i, sval (s i) (q ≫ pr i) y J := by
  have hm : q y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((q ≫ φ' a) ≫ pr i)) ⊓
      LB.wchart M' φ' (fun a => J' (q ≫ φ' a)) :=
    ⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ ((q ≫ φ' a) ≫ pr i), hJ'.mem _ q⟩
  have E := congrArg (gs q y _) (H (fun a i => J ((q ≫ φ' a) ≫ pr i)) (fun a => J' (q ≫ φ' a)))
  refine ((gs_mul q y _ hm _ _).trans (congrArg₂ (· * ·) ((gs_unit q y _ hm _).trans (congrArg Units.val
    (gm_linCombIso w φ' ε q y _ _ hm))) (gs_res q y _ hm _))).symm.trans (E.trans ((gs_prod q y _ hm _ _).trans
    (Finset.prod_congr rfl fun i _ => ?_)))
  rw [sval_of (s i) _ y J (fun a => J ((q ≫ φ' a) ≫ pr i)) (fun a => by rw [Category.assoc, ← hφ, Category.assoc])]
  exact (gs_res q y (hle _ _ i) hm _).trans (gs_pull q (pr i) y _ (hle _ _ i hm) _)
end ReciprocityTheory.ChartRestriction.G.DVR

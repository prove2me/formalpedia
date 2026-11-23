-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.box_gen_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:22:47.759203+00:00
-- url     : https://prove2.me/submissions/f058b027-f9ce-412d-8aea-49a83a08e940

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gm_linCombIso
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_rp__e27165827f88
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


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
theorem _root_.solution (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K] {Y₀ : Scheme.{0}}
    {φ' : K → (Y ⟶ X')} {φ : Fin j → K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (t' : LB.Gen (LB.LinComb M' φ' ε)) (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε))
    (H : LB.Gen.Maps (LB.linCombIso w φ' ε) t'
      (GeneratorPullback.boxGen M pr φ' ε (fun i => GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i))))
    (y : Y) {J J'} (hJ : Good M y J) (hJ' : Good M' y J') :
    (∏ a, bw w (φ' a) y (fun i => J (φ' a ≫ pr i)) (J' (φ' a)) ^ ε a) * val t' (𝟙 _) y J' = ∏ i, val (t i) (ρ i) y J := by
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J (φ' a ≫ pr i)) ⊓
      LB.wchart M' φ' (fun a => J' (φ' a)) :=
    ⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ (φ' a ≫ pr i), Set.mem_iInter.2 fun a => hJ' (φ' a)⟩
  have E := congrArg (gm (𝟙 Y) y (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J (φ' a ≫ pr i)) ⊓
    LB.wchart M' φ' (fun a => J' (φ' a)))) (H (fun a i => J (φ' a ≫ pr i), fun a => J' (φ' a)))
  have E₁ := gm_linCombIso w φ' ε (𝟙 Y) y _ _ hm
  simp only [Category.id_comp] at E₁
  rw [val_of t' _ y J' (fun a => J' (φ' a)) (fun a => by rw [Category.id_comp])]
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) E₁ (gm_res (𝟙 Y) y inf_le_right hm _))).symm.trans
    (E.symm.trans ((gm_res (𝟙 Y) y inf_le_left hm _).trans ?_))
  refine (map_prod (gm (𝟙 Y) y (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J (φ' a ≫ pr i))))
    (fun i => res (GeneratorPullback.box_le M pr φ' (fun a i => J (φ' a ≫ pr i)) i)
      ((GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i)).s (fun a _ => J (φ' a ≫ pr i)))) Finset.univ).trans
    (Finset.prod_congr rfl fun i _ => ?_)
  rw [val_of (t i) (ρ i) y J (fun a => J (φ' a ≫ pr i)) (fun a => congrArg J (hψ i a).symm)]
  exact (gm_res (𝟙 Y) y (GeneratorPullback.box_le M pr φ' _ i) hm.1 _).trans (gm_rp₁ (ρ i) y _ _ _ (GeneratorPullback.box_le M pr φ' _ i hm.1) _)
end ReciprocityTheory.ChartRestriction.G.DVR

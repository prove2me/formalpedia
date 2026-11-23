-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.glue_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:44.941858+00:00
-- url     : https://prove2.me/submissions/572cab69-cd34-4558-8fa0-7d8c686ec539

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_ext_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    {ι' : Type} (W : ι' → Y.Opens) (hW : ∀ y, ∃ s, y ∈ W s)
    (t : ∀ s, LB.Gen (LB.LinComb M (fun k => (W s).ι ≫ φ k) ε)) (ht : ∀ s, (t s).IsGen)
    (agree : ∀ s s' (Z : Scheme.{0}) (r : Z ⟶ (W s).toScheme) (r' : Z ⟶ (W s').toScheme) (z : Z) (J), Good M z J →
      r ≫ (W s).ι = r' ≫ (W s').ι → val (t s) r z J = val (t s') r' z J) :
    ∃ u : LB.Gen (LB.LinComb M φ ε), u.IsGen ∧ ∀ s (Z : Scheme.{0}) (r : Z ⟶ (W s).toScheme) (z : Z) (J), Good M z J →
      val u (r ≫ (W s).ι) z J = val (t s) r z J := by
  have glue : ∀ j : K → M.ι, ∃ a : Γ(Y, LB.wchart M φ j)ˣ, ∀ s (Z : Scheme.{0}) (r : Z ⟶ (W s).toScheme) (z : Z),
      r z ∈ LB.wchart M (fun k => (W s).ι ≫ φ k) j →
      gm (r ≫ (W s).ι) z _ a = gm r z (LB.wchart M (fun k => (W s).ι ≫ φ k) j) ((t s).s j) := by
    intro j
    choose b hb using fun s => exists_ext_unit (W s).ι (LB.wchart M (fun k => (W s).ι ≫ φ k) j) ((t s).s j)
    have le : ∀ s, (W s).ι ''ᵁ LB.wchart M (fun k => (W s).ι ≫ φ k) j ≤ LB.wchart M φ j := by
      rintro s _ ⟨y, hy, rfl⟩
      exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
    obtain ⟨a, ha⟩ := glue_unit (LB.wchart M φ j) _ le (fun y hy => by
        obtain ⟨s, hs⟩ := hW y
        exact Opens.mem_iSup.2 ⟨s, ⟨y, hs⟩, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k, rfl⟩) b (fun s s' y hy => by
        obtain ⟨⟨y₁, h₁, e₁⟩, ⟨y₂, h₂, e₂⟩⟩ := hy
        have hy₁ : y ∈ W s := e₁ ▸ y₁.2
        have hy₂ : y ∈ W s' := e₂ ▸ y₂.2
        let z : (W s ⊓ W s').toScheme := ⟨y, hy₁, hy₂⟩
        let r := Y.homOfLE (inf_le_left : W s ⊓ W s' ≤ W s)
        let r' := Y.homOfLE (inf_le_right : W s ⊓ W s' ≤ W s')
        have f₁ : r ≫ (W s).ι = (W s ⊓ W s').ι := Y.homOfLE_ι _
        have f₂ : r' ≫ (W s').ι = (W s ⊓ W s').ι := Y.homOfLE_ι _
        have hj : y ∈ LB.wchart M φ j := le s ⟨y₁, h₁, e₁⟩
        have m₁ : r z ∈ LB.wchart M (fun k => (W s).ι ≫ φ k) j := Set.mem_iInter.2 fun k =>
          (congrArg (fun q => φ k (q z) ∈ M.U (j k)) f₁).mpr (Set.mem_iInter.1 hj k)
        have m₂ : r' z ∈ LB.wchart M (fun k => (W s').ι ≫ φ k) j := Set.mem_iInter.2 fun k =>
          (congrArg (fun q => φ k (q z) ∈ M.U (j k)) f₂).mpr (Set.mem_iInter.1 hj k)
        choose I hI using fun χ : (W s ⊓ W s').toScheme ⟶ X => exists_chart hM (χ z)
        have c₁ := gen_trans (ht s) r z m₁ (Good.mem hI _ r)
        have c₂ := gen_trans (ht s') r' z m₂ (Good.mem hI _ r')
        have c₃ : trF (fun k => (W s).ι ≫ φ k) ε r z j (fun k => I (r ≫ (W s).ι ≫ φ k)) =
            trF (fun k => (W s').ι ≫ φ k) ε r' z j (fun k => I (r' ≫ (W s').ι ≫ φ k)) := by
          refine Finset.prod_congr rfl fun k _ => ?_
          have : r ≫ (W s).ι ≫ φ k = r' ≫ (W s').ι ≫ φ k := by rw [← Category.assoc, f₁, ← Category.assoc, f₂]
          show gm (r ≫ (W s).ι ≫ φ k) z (M.U (j k) ⊓ M.U (I (r ≫ (W s).ι ≫ φ k))) (M.g (j k) (I (r ≫ (W s).ι ≫ φ k))) ^ _ =
            gm (r' ≫ (W s').ι ≫ φ k) z (M.U (j k) ⊓ M.U (I (r' ≫ (W s').ι ≫ φ k))) (M.g (j k) (I (r' ≫ (W s').ι ≫ φ k))) ^ _
          rw [this]
        have b₁ := hb s _ r z m₁
        have b₂ := hb s' _ r' z m₂
        rw [f₁] at b₁
        rw [f₂] at b₂
        have n₁ : (W s ⊓ W s').ι z ∈ (W s).ι ''ᵁ LB.wchart M (fun k => (W s).ι ≫ φ k) j := ⟨y₁, h₁, e₁⟩
        have n₂ : (W s ⊓ W s').ι z ∈ (W s').ι ''ᵁ LB.wchart M (fun k => (W s').ι ≫ φ k) j := ⟨y₂, h₂, e₂⟩
        exact gm_inj (W s ⊓ W s').ι z n₁ n₂ (b₁.trans (c₁.trans ((congrArg₂ (· * ·) c₃
          (agree s s' _ r r' z I hI (f₁.trans f₂.symm))).trans (c₂.symm.trans b₂.symm)))))
    refine ⟨a, fun s Z r z hz => ?_⟩
    have hm : (r ≫ (W s).ι) z ∈ (W s).ι ''ᵁ LB.wchart M (fun k => (W s).ι ≫ φ k) j := ⟨r z, hz, rfl⟩
    exact (gm_res _ z (le s) hm a).symm.trans ((congrArg (gm _ z _) (ha s)).trans (hb s Z r z hz))
  choose a ha using glue
  refine ⟨⟨a⟩, fun j j' => unit_ext fun y hy => ?_, fun s Z r z J hJ => ?_⟩
  · obtain ⟨s, hs⟩ := hW y
    let z : (W s).toScheme := ⟨y, hs⟩
    have m₁ : (𝟙 _ : (W s).toScheme ⟶ _) z ∈ LB.wchart M (fun k => (W s).ι ≫ φ k) j :=
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 k
    have m₂ : (𝟙 _ : (W s).toScheme ⟶ _) z ∈ LB.wchart M (fun k => (W s).ι ≫ φ k) j' :=
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k
    have a₁ := ha j s _ (𝟙 _) z m₁
    have a₂ := ha j' s _ (𝟙 _) z m₂
    rw [Category.id_comp] at a₁ a₂
    have hz : (W s).ι z ∈ LB.wchart M φ j ⊓ LB.wchart M φ j' := hy
    refine gm_inj (W s).ι z hz hz (((gm_res _ z _ hz _).trans (a₁.trans (gen_trans (ht s) (𝟙 _) z m₁ m₂))).trans (Eq.symm ?_))
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb M φ ε (W s).ι z j j' hz.1 hz.2).trans ?_)
      ((gm_res _ z _ hz _).trans a₂))
    simp only [trF, Category.id_comp]
  · rw [val_of _ (r ≫ (W s).ι) z J (fun k => J (r ≫ (W s).ι ≫ φ k)) (fun k => by rw [Category.assoc])]
    exact ha _ s Z r z (hJ.mem _ r)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor

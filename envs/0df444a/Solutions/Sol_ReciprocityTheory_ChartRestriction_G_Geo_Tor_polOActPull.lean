-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.polOActPull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:41:03.000162+00:00
-- url     : https://prove2.me/submissions/3d8c5d29-96f0-420a-b41d-1828a084841f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_down
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isMonHom_of_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_ros


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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution : PolOActPullSt := by
  intro S S' f P P' g hg hw O _ _ o
  have inj : ∀ {T : Over S'} {x y : T ⟶ P'.A}, pushPt hg.1.w x = pushPt hg.1.w y → x = y := fun {T x y} h =>
    Over.OverMorphism.ext (hg.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  let act : O → (P'.A ⟶ P'.A) := fun a => Over.homMk (hg.1.lift (g ≫ (o.act a).left) P'.A.hom
    (by rw [Category.assoc, Over.w, hg.1.w])) (hg.1.lift_snd _ _ _)
  have ha : ∀ a, (act a).left ≫ g = g ≫ (o.act a).left := fun a => hg.1.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ P'.A) a, pushPt hg.1.w (x ≫ act a) = pushPt hg.1.w x ≫ o.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have pm : ∀ {T : Over S'} (x y : T ⟶ P'.A), pushPt hg.1.w (x * y) = pushPt hg.1.w x * pushPt hg.1.w y := fun x y =>
    map_mul (pushHom hg _) x y
  obtain ⟨w, gw'⟩ := LBIso.symm hw
  refine ⟨⟨⟨act, fun a => isMonHom_of_mul _ fun T x y => inj ?_, inj ?_, fun a b => inj ?_, fun a b => inj ?_⟩,
    fun a s => ?_⟩, ha⟩
  · have := o.hom a
    rw [pa, pm, pm, pa, pa, MonObj.mul_comp]
  · rw [← Category.id_comp (act 1), pa, o.map_one, Category.comp_id]
  · rw [← Category.id_comp (act (a * b)), pa, pa, ← Category.id_comp (act b), pa, o.map_mul, Category.assoc]
  · refine Eq.trans ?_ (pm (act a) (act b)).symm
    rw [← Category.id_comp (act (a + b)), ← Category.id_comp (act a), ← Category.id_comp (act b), pa, pa, pa, o.map_add]
    exact MonObj.comp_mul _ _ _
  · obtain ⟨U, hU, t, ht⟩ := o.rosati a (f s)
    let V : (P'.A ⊗ P'.A).left.Opens := (P'.A ⊗ P'.A).hom ⁻¹ᵁ (f ⁻¹ᵁ U)
    let T' : Over S' := Over.mk (V.ι ≫ (P'.A ⊗ P'.A).hom)
    let j : T' ⟶ P'.A ⊗ P'.A := Over.homMk V.ι rfl
    let m := lift (pushPt hg.1.w (j ≫ fst _ _)) (pushPt hg.1.w (j ≫ snd _ _))
    obtain ⟨n, hn⟩ : ∃ n : V.toScheme ⟶ ((P.A ⊗ P.A).hom ⁻¹ᵁ U).toScheme, n ≫ ((P.A ⊗ P.A).hom ⁻¹ᵁ U).ι = m.left :=
      ⟨IsOpenImmersion.lift _ m.left (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact (congrArg (fun q => q y ∈ U) (Over.w m)).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨t', ht', -⟩ := exists_gen P.isLB (φ' := fun i => (V.ι ≫ rosatiφ P'.A (act a) (act (star a)) i) ≫ g)
      (ε' := rosatiε) (fun W _ k => by
        have p₁ := prod_ros (o.act a) (o.act (star a)) (pushPt hg.1.w (j ≫ fst _ _)) (pushPt hg.1.w (j ≫ snd _ _)) k
        have p₂ := prod_ros (act a) (act (star a)) (j ≫ fst _ _) (j ≫ snd _ _) (fun q => k (q ≫ g))
        rw [← comp_lift, lift_fst_snd, Category.comp_id] at p₂
        rw [← pa, ← pa, ← pm, ← pm] at p₁
        exact ((Finset.prod_congr rfl fun i _ => by
          show k (n ≫ _ ≫ _) ^ _ = k (m.left ≫ _) ^ _
          rw [← Category.assoc, hn]).trans p₁).trans p₂.symm) (LB.pullGen P.L _ _ t n) (pullGen_isGen _ _ _ _ ht n)
    exact ⟨f ⁻¹ᵁ U, hU, exists_down ((isGen_iff w).1 gw') P.isLB P'.isLB t' ht'⟩
end ReciprocityTheory.ChartRestriction.G.Geo.Tor

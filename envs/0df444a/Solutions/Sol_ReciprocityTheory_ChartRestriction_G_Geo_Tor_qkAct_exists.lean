-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.qkAct_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:08:58.303877+00:00
-- url     : https://prove2.me/submissions/79a64fed-927a-4aa3-a7dd-56a7eca9d8b0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_gt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cPoint_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isAdd_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isZero_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isIota_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_qk_equiv_refl
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__944b82dcaa95
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gt_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tau_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_ros
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gen_unique
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_ros
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_ros_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
variable {O : Type} [CommRing O] [StarRing O] [Module O D.X]
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (hG : GlobalFnsSt) (hB : D.TauBimult) (oa : D.OAct O) {k : ℕ} (a : O) (p : QkPt D F k) :
    ∃ p', QkAct oa a p p' := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have hr := oa.onB.rosati (star a)
  have hbal := oa.tau_bal (star a)
  rw [star_star] at hr hbal
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.P.isAb D.P.isLB _ _ hr
  have cf : ∀ (T) (x : O) χ, cP D T (x • χ) = cP D T χ ≫ oa.onB.act x := fun T x χ => by
    rw [cP, oa.c_lin, ← Category.assoc]; rfl
  have ra := fun {y : (TF (R := R) F).left} {J} (hJ : Good D.P.L y J) =>
    ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := TF (R := R) F) hJ
  have vu : ∀ {y : (TF (R := R) F).left} {J}, Good D.P.L y J → ∀ x w : TF (R := R) F ⟶ D.P.A,
      val (LB.pullGen D.P.L _ _ u (lift x w).left) (𝟙 _) y J = val₂ u y J x w := fun hJ x w => by
    rw [val_pull hJ, Category.id_comp]; rfl
  have u₁ : ∀ {y : (TF (R := R) F).left} {J}, Good D.P.L y J → ∀ w, val₂ u y J 1 w = 1 := fun {y J} hJ w => by
    have C : IsCub (cubV D.cub y J) := isCub_cubV D.cub hJ
    have e := (ra hJ 1 1 w).1
    rw [_root_.mul_one, MonObj.one_comp, C.face, C.face, _root_.mul_one, _root_.one_mul] at e
    exact mul_eq_left.1 e.symm
  have u₂ : ∀ {y : (TF (R := R) F).left} {J}, Good D.P.L y J → ∀ w, val₂ u y J w 1 = 1 := fun {y J} hJ w => by
    have C : IsCub (cubV D.cub y J) := isCub_cubV D.cub hJ
    have e := (ra hJ 1 1 w).2
    rw [_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
    exact mul_eq_left.1 e.symm
  have ex : ∀ g : GtPtF D F, ∃ g' : GtPtF D F, g'.b = g.b ≫ oa.onB.act a ∧ ∀ χ y J, Good D.P.L y J →
      val (g'.s χ) (𝟙 _) y J = val (g.s (star a • χ)) (𝟙 _) y J * val₂ u y J (cP D _ χ) g.b := by
    intro g
    have vv : ∀ χ y J, Good D.P.L y J → val (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left)) (𝟙 _) y J =
        val (g.s (star a • χ)) (𝟙 _) y J * val₂ u y J (cP D _ χ) g.b := fun χ y J hJ =>
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (vu hJ _ _))
    obtain ⟨g', hb, hv⟩ := exists_gt (g.b ≫ oa.onB.act a) (fun χ => LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left))
      (fun χ => mulGen_isGen _ _ _ _ _ _ _ (g.isGen _) (pullGen_isGen _ _ _ _ hu _)) (fun χ U _ h => by
        refine (prod_sum₂ (K := Fin 4) (K' := Fin 6) (U := U) _ (prod_gt g.b (star a • χ) h)
          (prod_ros _ _ (cP D _ χ) g.b h)).trans ?_
        rw [prod_gt, cf]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel) (fun y J hJ => by
        rw [vv 0 y J hJ, smul_zero, cPoint_zero, u₁ hJ, _root_.mul_one]
        exact (val_corr hJ g.s_zero _).trans (val_one _)) (fun χ χ' y J hJ => by
        have e₁ := (ra hJ (cP D _ χ) (cP D _ χ') g.b).1
        have e₂ := gt_mul (𝟙 (TF (R := R) F)) hJ g (star a • χ) (star a • χ')
        rw [Category.id_comp, cf, cf, Over.id_left] at e₂
        rw [vv _ y J hJ, vv _ y J hJ, vv _ y J hJ, smul_add, cPoint_add, _root_.mul_assoc]
        refine (congrArg _ e₁).trans ?_
        rw [← _root_.mul_assoc]
        exact (congrArg (· * _) e₂).trans (mul_mul_mul_comm _ _ _ _))
    exact ⟨g', hb, fun χ y J hJ => (hv χ y J hJ).trans (vv χ y J hJ)⟩
  choose act hb hv using ex
  have add : ∀ g g' g'' : GtPtF D F, g.IsAdd g' g'' → (act g).IsAdd (act g') (act g'') := fun g g' g'' h => by
    obtain ⟨b₁, v₁⟩ := (isAdd_iff _ _ _).1 h
    refine (isAdd_iff _ _ _).2 ⟨by rw [hb, hb, hb, b₁, MonObj.mul_comp], fun χ y J hJ => ?_⟩
    have e₁ := (ra hJ g.b g'.b (cP D _ χ)).2
    have e₂ := v₁ (star a • χ) y J hJ
    rw [cf] at e₂
    rw [← b₁] at e₁
    rw [hv _ _ y J hJ, hv _ _ y J hJ, hv _ _ y J hJ, hb, hb, _root_.mul_assoc]
    refine (congrArg _ e₁).trans ?_
    rw [← _root_.mul_assoc]
    exact (congrArg (· * _) e₂).trans (mul_mul_mul_comm _ _ _ _)
  obtain ⟨h, ⟨gs, g₀, gst, gl⟩, hι⟩ := p.eq
  obtain ⟨ιb, ιv⟩ := (isIota_iff _ _).1 hι
  let q : QkPt D F k := ⟨a • p.y, act p.g, act h, ⟨fun i => act (gs i), by
      obtain ⟨z₁, z₂⟩ := (isZero_iff _).1 g₀
      exact (isZero_iff _).2 ⟨by rw [hb, z₁, MonObj.one_comp], fun χ y J hJ => by
        rw [hv _ _ y J hJ, z₂ _ y J hJ, z₁, u₂ hJ, _root_.mul_one]⟩,
      fun i => add _ _ _ (gst i), congrArg act gl⟩, (isIota_iff _ _).2 ⟨by rw [hb, ιb, cf], fun χ y J hJ => by
      let κ : TF (R := R) F ⟶ TK R := Over.homMk (𝟙 _ ≫ jFK (R := R) F) (by
        rw [Category.id_comp]; rfl)
      have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hbal u hu u₀ χ p.y) κ.left)
      have e' : val (LB.pullGen D.P.L _ _ u (D.pt2 χ p.y)) κ.left y J = val₂ u y J (cP D _ χ) (cP D _ p.y) := by
        rw [val_pull hJ, val₂, ← comp_cP D κ, ← comp_cP D κ p.y, ← comp_lift]; rfl
      rw [hv _ _ y J hJ, ιv _ y J hJ, ιb, ← e']
      exact (congrArg₂ (· * ·) (tau_symm (𝟙 (TF (R := R) F)) hJ _ _) rfl).trans
        (e.trans (tau_symm (𝟙 (TF (R := R) F)) hJ _ _))⟩⟩
  refine ⟨q, q, rfl, ⟨hb _, fun u' hu' u₀' χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩, qk_equiv_refl hB q⟩
  refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) rfl ?_) (hv p.g χ y J hJ).symm)
  rw [val_pull hJ, Category.id_comp]
  have z2 : zero2 D.P.A ≫ (snd D.P.A D.P.A).left ≫ D.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift η[D.P.A] η[D.P.A])
  exact gen_unique D.P.isLB _ (zero2 D.P.A) z2 (surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2) hu' hu
    (fun y I hI => by
      have a₁ := val_corr hI u₀' (𝟙 _)
      have a₂ := val_corr hI u₀ (𝟙 _)
      rw [val_pull hI, Category.id_comp] at a₁ a₂
      exact a₁.trans a₂.symm) _ _ y J hJ
end ReciprocityTheory.ChartRestriction.G.Geo.Tor

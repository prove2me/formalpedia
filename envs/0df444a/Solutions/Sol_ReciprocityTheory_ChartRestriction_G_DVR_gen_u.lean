-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.gen_u
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:36:34.898957+00:00
-- url     : https://prove2.me/submissions/b0a85477-2baf-4c4e-9c17-c6c923d925d4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_surj_appTop
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_pr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_fam
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__8d4277abb339
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_cubN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gen_unique
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (hG : GlobalFnsSt) (k : ℕ) (α α' : D.X) (m : TF (R := R) F ⟶ D.P.A)
    (hα : cP D _ α' = cP D _ α * m ^ k) {K : Type} [Fintype K] {φ : K → ((TF (R := R) F).left ⟶ D.P.A.left)} {ε : K → ℤ}
    (v : LB.Gen (LB.LinComb D.P.L φ ε)) (hv : v.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (h : ((TF (R := R) F).left ⟶ D.P.A.left) → U), ∏ i, h (φ i) ^ ε i =
      (h (cP D _ α * m).left)⁻¹ * h (cP D _ α).left * h m.left * (h (1 : TF (R := R) F ⟶ D.P.A).left)⁻¹ *
        (h m.left ^ k)⁻¹ * h (1 : TF (R := R) F ⟶ D.P.A).left ^ k) :
    (∃ u : LB.Gen (LB.LinComb D.P.L (Sum.elim (DegPre.famφ D F α')
        (fun i => (DegPre.trPt D F m).left ≫ DegPre.famφ D F α i)) (DegPre.deltaε k)), u.IsGen ∧
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) v) ∧
    ∀ u : LB.Gen (LB.LinComb D.P.L (Sum.elim (DegPre.famφ D F α')
        (fun i => (DegPre.trPt D F m).left ≫ DegPre.famφ D F α i)) (DegPre.deltaε k)), u.IsGen →
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) v →
      ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J →
        val u ρ.left z J = uVal D F k α m ρ z J * val v (ρ ≫ fst _ _).left z J := by
  let a : DegPre.BF D F ⟶ D.P.A := cP D _ α
  let mm : DegPre.BF D F ⟶ D.P.A := fst _ _ ≫ m
  let x : DegPre.BF D F ⟶ D.P.A := DegPre.prB D F
  have hα' : cP D (DegPre.BF D F) α' = a * mm ^ k := by
    rw [← comp_cP D (fst (TF (R := R) F) D.P.A), hα]
    exact (map_mul (preHom (fst (TF (R := R) F) D.P.A)) _ _).trans
      (congrArg₂ (· * ·) (comp_cP D _ α) (map_pow (preHom (fst (TF (R := R) F) D.P.A)) _ _))
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub a mm x k
  obtain ⟨u₀, hu₀, vu₀⟩ := exists_gen D.P.isLB (φ' := Sum.elim (DegPre.famφ D F α')
      (fun i => (DegPre.trPt D F m).left ≫ DegPre.famφ D F α i)) (ε' := DegPre.deltaε k) (fun U _ h => by
      have p₁ := prod_cub a x mm h
      have p₂ := hF U (fun q => h ((fst (TF (R := R) F) D.P.A).left ≫ q))
      have p₃ := prod_fam D F (𝟙 _) α' k h
      have p₄ := prod_fam D F (DegPre.trPt D F m) α k h
      have q₁ : (fst (TF (R := R) F) D.P.A).left ≫ (cP D _ α * m).left = (a * mm).left :=
        congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left) ((MonObj.comp_mul (fst (TF (R := R) F) D.P.A) (cP D _ α) m).trans
          (congrArg (· * mm) (comp_cP D (fst (TF (R := R) F) D.P.A) α)))
      have q₂ : (fst (TF (R := R) F) D.P.A).left ≫ (cP D _ α).left = a.left :=
        congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left) (comp_cP D (fst (TF (R := R) F) D.P.A) α)
      have q₃ : (fst (TF (R := R) F) D.P.A).left ≫ (1 : TF (R := R) F ⟶ D.P.A).left = (1 : DegPre.BF D F ⟶ D.P.A).left :=
        congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (fst (TF (R := R) F) D.P.A))
      have q₄ : (fst (TF (R := R) F) D.P.A).left ≫ m.left = mm.left := rfl
      rw [q₁, q₂, q₃, q₄] at p₂
      simp only [Over.id_left, Category.id_comp] at p₃
      rw [hα'] at p₃
      rw [tr_pr] at p₄
      refine Eq.trans (prod_sum₂ (K := Fin 8 ⊕ thK) (K' := K) (U := U) _
        (prod_sum₂ (K := Fin 8) (K' := thK) (U := U) _ rfl (prod_neg _ _ p₁)) p₂)
        (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)).symm)
      rw [← _root_.mul_assoc (cP D _ α), mul_comm mm x]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, a, mm, x]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ N (LB.invGen D.P.L _ _
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift a (lift x mm)).left)))
      (LB.pullGen D.P.L _ _ v (fst (TF (R := R) F) D.P.A).left))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen _)))
      (pullGen_isGen _ _ _ _ hv _))
  have val₀ : ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J →
      val u₀ ρ.left z J = uVal D F k α m ρ z J * val v (ρ ≫ fst _ _).left z J := fun T ρ z J hJ => by
    refine (vu₀ _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      ((congrArg₂ (· * ·) (vN T ρ z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹) (val_cub D.cub ρ hJ _ _ _)))).trans ?_))
      (val_pull hJ _ _ _)))
    rw [uVal, ← comp_cP D ρ α]
  have z₁ : DegPre.zF D F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF D F ≫ DegPre.prB D F = 1 := lift_snd _ _
  have at₀ : ∀ y J, Good D.P.L y J → val u₀ (DegPre.zF D F).left y J = val v (𝟙 _) y J := fun y J hJ => by
    have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
    rw [val₀ _ _ y J hJ, uVal, z₂, z₁, C.N_one, C.face₂, inv_one, _root_.one_mul, _root_.one_mul]; rfl
  refine ⟨⟨u₀, hu₀, corr_of_val D.P.isLB fun y J hJ => ?_⟩, fun u hu hc T ρ z J hJ => ?_⟩
  · rw [val_pull hJ, Category.id_comp]; exact at₀ y J hJ
  · refine (gen_unique D.P.isLB (fst (TF (R := R) F) D.P.A).left (DegPre.zF D F).left (congrArg (fun q => q.left) z₁)
      (surj_appTop D F hG) hu hu₀ (fun y J hJ => ?_) _ ρ.left z J hJ).trans (val₀ T ρ z J hJ)
    have := val_corr hJ hc (𝟙 _)
    rw [val_pull hJ, Category.id_comp] at this
    exact this.trans (at₀ y J hJ).symm
end ReciprocityTheory.ChartRestriction.G.DVR

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TWM.gen_uO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:51:43.497071+00:00
-- url     : https://prove2.me/submissions/a6e53902-fbec-46ea-9113-bca3f3a7c5b6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TWMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LiftOUnique
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TWM_trO_snd
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_prod_famB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_cubN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
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
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TWM
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing TWO SectionScalarValuation
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
namespace ReciprocityTheory.ChartRestriction.G.DVR.TWM
theorem _root_.solution (k : ℕ) (α α' : D.toPre.X) (m : TO hϖ hv ⟶ D.toPre.P.A)
    (hα : cP D.toPre _ α' = cP D.toPre _ α * m ^ k) {K : Type} [Fintype K]
    {φ : K → ((TO hϖ hv).left ⟶ D.toPre.P.A.left)} {ε : K → ℤ}
    (vO : LB.Gen (LB.LinComb D.toPre.P.L φ ε)) (hvO : vO.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (h : ((TO hϖ hv).left ⟶ D.toPre.P.A.left) → U), ∏ i, h (φ i) ^ ε i =
      (h (cP D.toPre _ α * m).left)⁻¹ * h (cP D.toPre _ α).left * h m.left * (h (1 : TO hϖ hv ⟶ D.toPre.P.A).left)⁻¹ *
        (h m.left ^ k)⁻¹ * h (1 : TO hϖ hv ⟶ D.toPre.P.A).left ^ k) :
    ∃ u : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (fun i => (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α' i)
        (fun i => (trO hϖ hv m ≫ snd _ _).left ≫ D.toPre.famφB α i)) (DegPre.deltaε k)), u.IsGen ∧
      ∀ (T : Over (Spec (CommRingCat.of V))) (ρ : T ⟶ TO hϖ hv ⊗ D.toPre.P.A) (z : T.left) (J), Good D.toPre.P.L z J →
        val u ρ.left z J = cubN (th D.toPre z J) k (cP D.toPre T α) (ρ ≫ fst _ _ ≫ m) (ρ ≫ snd _ _) *
          (th D.toPre z J (cP D.toPre T α) (ρ ≫ snd _ _) (ρ ≫ fst _ _ ≫ m))⁻¹ * val vO (ρ ≫ fst _ _).left z J := by
  let a : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A := cP D.toPre _ α
  let mm : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A := fst _ _ ≫ m
  let x : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A := snd _ _
  have hα' : cP D.toPre (TO hϖ hv ⊗ D.toPre.P.A) α' = a * mm ^ k := by
    rw [← comp_cP D.toPre (fst (TO hϖ hv) D.toPre.P.A), hα]
    exact (map_mul (preHom (fst (TO hϖ hv) D.toPre.P.A)) _ _).trans
      (congrArg₂ (· * ·) (comp_cP D.toPre _ α) (map_pow (preHom (fst (TO hϖ hv) D.toPre.P.A)) _ _))
  obtain ⟨N, hN, vN⟩ := exists_cubN D.toPre.cub a mm x k
  obtain ⟨u₀, hu₀, vu₀⟩ := exists_gen D.toPre.P.isLB (φ' := Sum.elim (fun i => (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α' i)
      (fun i => (trO hϖ hv m ≫ snd _ _).left ≫ D.toPre.famφB α i)) (ε' := DegPre.deltaε k) (fun U _ h => by
      have p₁ := prod_cub a x mm h
      have p₂ := hF U (fun q => h ((fst (TO hϖ hv) D.toPre.P.A).left ≫ q))
      have p₃ := SectionScalarValuation.prod_famB D.toPre (snd (TO hϖ hv) D.toPre.P.A) α' k h
      have p₄ := SectionScalarValuation.prod_famB D.toPre (trO hϖ hv m ≫ snd _ _) α k h
      have q₁ : (fst (TO hϖ hv) D.toPre.P.A).left ≫ (cP D.toPre _ α * m).left = (a * mm).left :=
        congrArg (fun q : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A => q.left)
          ((MonObj.comp_mul (fst (TO hϖ hv) D.toPre.P.A) (cP D.toPre _ α) m).trans
            (congrArg (· * mm) (comp_cP D.toPre (fst (TO hϖ hv) D.toPre.P.A) α)))
      have q₂ : (fst (TO hϖ hv) D.toPre.P.A).left ≫ (cP D.toPre _ α).left = a.left :=
        congrArg (fun q : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A => q.left) (comp_cP D.toPre (fst (TO hϖ hv) D.toPre.P.A) α)
      have q₃ : (fst (TO hϖ hv) D.toPre.P.A).left ≫ (1 : TO hϖ hv ⟶ D.toPre.P.A).left =
          (1 : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A).left :=
        congrArg (fun q : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A => q.left) (MonObj.comp_one (M := D.toPre.P.A) (fst (TO hϖ hv) D.toPre.P.A))
      have q₄ : (fst (TO hϖ hv) D.toPre.P.A).left ≫ m.left = mm.left := rfl
      rw [q₁, q₂, q₃, q₄] at p₂
      have c₁ : SectionScalarValuation.cQ D.toPre (TO hϖ hv ⊗ D.toPre.P.A) α' = a * mm ^ k := hα'
      have c₂ : SectionScalarValuation.cQ D.toPre (TO hϖ hv ⊗ D.toPre.P.A) α = a := rfl
      rw [c₁] at p₃
      rw [c₂] at p₄
      conv at p₄ => rhs; rw [trO_snd]
      refine Eq.trans (prod_sum₂ (K := Fin 8 ⊕ thK) (K' := K) (U := U) _
        (prod_sum₂ (K := Fin 8) (K' := thK) (U := U) _ rfl (prod_neg _ _ p₁)) p₂)
        (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)).symm)
      have r1 : x * (a * mm ^ k) = a * mm ^ k * x := mul_comm _ _
      have r2 : x * mm * a = a * x * mm := by rw [mul_comm, ← _root_.mul_assoc]
      have r3 : mm * x = x * mm := mul_comm _ _
      rw [r1, r2, r3]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, a, mm, x]
      module)
    (LB.mulGen D.toPre.P.L _ _ _ _ (LB.mulGen D.toPre.P.L _ _ _ _ N (LB.invGen D.toPre.P.L _ _
      (LB.pullGen D.toPre.P.L (thφ D.toPre.P.A (x3 D.toPre.P.A)) thε D.toPre.cub.t (lift a (lift x mm)).left)))
      (LB.pullGen D.toPre.P.L _ _ vO (fst (TO hϖ hv) D.toPre.P.A).left))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.toPre.cub.isGen _)))
      (pullGen_isGen _ _ _ _ hvO _))
  refine ⟨u₀, hu₀, fun T ρ z J hJ => ?_⟩
  refine (vu₀ _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    ((congrArg₂ (· * ·) (vN T ρ z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹) (val_cub D.toPre.cub ρ hJ _ _ _)))).trans ?_))
    (val_pull hJ _ _ _)))
  rw [← comp_cP D.toPre ρ α]
end ReciprocityTheory.ChartRestriction.G.DVR.TWM

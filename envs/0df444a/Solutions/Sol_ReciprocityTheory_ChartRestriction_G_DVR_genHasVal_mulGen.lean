-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.genHasVal_mulGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:02:26.547622+00:00
-- url     : https://prove2.me/submissions/f1918530-8c0e-4389-ba96-de9c9f493b38

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_genHasVal_units
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen


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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
set_option maxHeartbeats 1000000
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (hϖ : Irreducible ϖ) {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) {Ix Ix' : Type} [Fintype Ix] [Fintype Ix']
    (φ₁ : Ix → (Spec (CommRingCat.of V) ⟶ X)) (φ₁' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ₁ : ∀ k, φ₁' k = jK V ≫ φ₁ k) (ε₁ : Ix → ℤ)
    (φ₂ : Ix' → (Spec (CommRingCat.of V) ⟶ X)) (φ₂' : Ix' → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ₂ : ∀ k, φ₂' k = jK V ≫ φ₂ k) (ε₂ : Ix' → ℤ)
    (t₁ : LB.Gen (LB.LinComb L φ₁' ε₁)) (t₂ : LB.Gen (LB.LinComb L φ₂' ε₂)) {n m : ℤ}
    (hn : GenHasVal ϖ L φ₁ φ₁' hφ₁ ε₁ t₁ n) (hm : GenHasVal ϖ L φ₂ φ₂' hφ₂ ε₂ t₂ m) :
    GenHasVal ϖ L (Sum.elim φ₁ φ₂) (Sum.elim φ₁' φ₂') (sumElim_hφ hφ₁ hφ₂) (Sum.elim ε₁ ε₂)
      (LB.mulGen L φ₁' ε₁ φ₂' ε₂ t₁ t₂) (n + m) := by
  obtain ⟨e₁, he₁, c₁, hc₁, hC₁⟩ := genHasVal_units L φ₁ φ₁' hφ₁ ε₁ t₁ hn
  obtain ⟨e₂, he₂, c₂, hc₂, hC₂⟩ := genHasVal_units L φ₂ φ₂' hφ₂ ε₂ t₂ hm
  refine ⟨LB.mulGen L φ₁ ε₁ φ₂ ε₂ e₁ e₂, mulGen_isGen L φ₁ ε₁ φ₂ ε₂ e₁ e₂ he₁ he₂, c₁ * c₂, ?_,
    fun (j : Ix ⊕ Ix' → L.ι) => ?_⟩
  · obtain ⟨u₁, hu₁⟩ := hc₁
    obtain ⟨u₂, hu₂⟩ := hc₂
    refine ⟨u₁ * u₂, ?_⟩
    have hπ : algebraMap V (FractionRing V) ϖ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hϖ.ne_zero
    rw [hu₁, hu₂, zpow_add₀ hπ, Units.val_mul, map_mul]
    ring
  · have gen1 : ∀ (W W' : (Spec (CommRingCat.of (FractionRing V))).Opens) (h : W' ≤ W)
        (x : Γ(Spec (CommRingCat.of (FractionRing V)), ⊤)),
        ((Spec (CommRingCat.of (FractionRing V))).presheaf.map (homOfLE h).op).hom (resTop W x) =
          resTop W' x := by
      intro W W' h x
      simp only [resTop]
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    have gen2 : ∀ {A B : Scheme.{0}} (f : A ⟶ B) (U U' : B.Opens) (hU : U' ≤ U) (W : A.Opens)
        (hW : W ≤ f ⁻¹ᵁ U') (x : Γ(B, U)ˣ),
        res hW (pullU f U' (res hU x)) = res (fun y hy => hU (hW hy) : W ≤ f ⁻¹ᵁ U) (pullU f U x) := by
      intro A B f U U' hU W hW x
      apply Units.ext
      have hm : (B.presheaf.map (homOfLE hU).op ≫ f.app U') ≫ A.presheaf.map (homOfLE hW).op =
          f.app U ≫ A.presheaf.map (homOfLE (fun y hy => hU (hW hy) : W ≤ f ⁻¹ᵁ U)).op := by
        rw [Scheme.Hom.naturality, Category.assoc, ← Functor.map_comp]
        rfl
      exact congrArg (fun m => m.hom x.val) hm
    have gen3 : ∀ {A : Scheme.{0}} {U U' U'' : A.Opens} (h1 : U' ≤ U) (h2 : U'' ≤ U') (x : Γ(A, U)ˣ),
        res h2 (res h1 x) = res (h2.trans h1) x := by
      intro A U U' U'' h1 h2 x
      apply Units.ext
      have hm : A.presheaf.map (homOfLE h1).op ≫ A.presheaf.map (homOfLE h2).op =
          A.presheaf.map (homOfLE (h2.trans h1)).op := by
        rw [← Functor.map_comp]
        rfl
      exact congrArg (fun m => m.hom x.val) hm
    have key2 : ∀ {W W1 W2 : (Spec (CommRingCat.of (FractionRing V))).Opens}
        {U U1 U2 : (Spec (CommRingCat.of V)).Opens} (a1 : W ≤ W1) (a2 : W ≤ W2)
        (b1 : W1 ≤ jK V ⁻¹ᵁ U1) (b2 : W2 ≤ jK V ⁻¹ᵁ U2) (m1 : U ≤ U1) (m2 : U ≤ U2)
        (h : W ≤ jK V ⁻¹ᵁ U) (E1 : Γ(Spec (CommRingCat.of V), U1)ˣ) (E2 : Γ(Spec (CommRingCat.of V), U2)ˣ)
        (T1 C1 : Γ(Spec (CommRingCat.of (FractionRing V)), W1)ˣ)
        (T2 C2 : Γ(Spec (CommRingCat.of (FractionRing V)), W2)ˣ) (c1 c2 : FractionRing V),
        T1 = C1 * res b1 (pullU (jK V) U1 E1) → T2 = C2 * res b2 (pullU (jK V) U2 E2) →
        C1.val = resTop W1 (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c1) →
        C2.val = resTop W2 (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c2) →
        (res a1 T1 * res a2 T2).val = resTop W (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) (c1 * c2)) *
          (res h (pullU (jK V) U (res m1 E1 * res m2 E2))).val := by
      intro W W1 W2 U U1 U2 a1 a2 b1 b2 m1 m2 h E1 E2 T1 C1 T2 C2 c1 c2 h1 h2 h3 h4
      have e1 : (res a1 C1).val = resTop W (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c1) := by
        rw [← gen1 W1 W a1, ← h3]
        rfl
      have e2 : (res a2 C2).val = resTop W (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c2) := by
        rw [← gen1 W2 W a2, ← h4]
        rfl
      have e3 : resTop W (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) (c1 * c2)) =
          resTop W (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c1) *
            resTop W (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c2) := by
        simp only [scal, resTop, map_mul]
      rw [h1, h2, map_mul, map_mul, gen3, gen3, map_mul (pullU (jK V) U), map_mul (res h), gen2, gen2]
      simp only [Units.val_mul]
      rw [e1, e2, e3]
      ring
    obtain ⟨C₁, hC₁v, hC₁e⟩ := hC₁ (j ∘ Sum.inl)
    obtain ⟨C₂, hC₂v, hC₂e⟩ := hC₂ (j ∘ Sum.inr)
    exact key2 _ _ _ _ _ _ _ _ _ _ C₁ _ C₂ _ _ hC₁e hC₂e hC₁v hC₂v
end ReciprocityTheory.ChartRestriction.G.DVR

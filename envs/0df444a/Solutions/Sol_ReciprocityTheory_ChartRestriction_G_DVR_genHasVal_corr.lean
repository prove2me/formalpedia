-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.genHasVal_corr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:26:46.050856+00:00
-- url     : https://prove2.me/submissions/26203fab-1912-4628-a146-08522302e162

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_exists_genHasVal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_eq_top_of_closedPoint_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_genHasVal_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_hasVal_mul_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_hasVal_unique


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
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (hϖ : Irreducible ϖ) {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) {Ix Ix' : Type}
    [Fintype Ix] [Fintype Ix'] (s : X ⟶ Spec (CommRingCat.of V)) [IsSeparated s]
    (φ₁ : Ix → (Spec (CommRingCat.of V) ⟶ X)) (φ₁' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ₁ : ∀ k, φ₁' k = jK V ≫ φ₁ k) (ε₁ : Ix → ℤ)
    (φ₂ : Ix' → (Spec (CommRingCat.of V) ⟶ X)) (φ₂' : Ix' → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ₂ : ∀ k, φ₂' k = jK V ≫ φ₂ k) (ε₂ : Ix' → ℤ)
    (hs₁ : ∀ k, φ₁ k ≫ s = 𝟙 _) (hs₂ : ∀ k, φ₂ k ≫ s = 𝟙 _)
    (t₁ : LB.Gen (LB.LinComb L φ₁' ε₁)) (t₂ : LB.Gen (LB.LinComb L φ₂' ε₂)) (ht₂ : t₂.IsGen)
    (hc : LB.Gen.Corr L φ₁' ε₁ φ₂' ε₂ t₁ t₂) {n : ℤ} (hn : GenHasVal ϖ L φ₁ φ₁' hφ₁ ε₁ t₁ n) :
    GenHasVal ϖ L φ₂ φ₂' hφ₂ ε₂ t₂ n := by
  obtain rfl : φ₁' = fun k => jK V ≫ φ₁ k := funext hφ₁
  obtain rfl : φ₂' = fun k => jK V ≫ φ₂ k := funext hφ₂
  have sep : ∀ (x x' : Spec (CommRingCat.of V) ⟶ X), jK V ≫ x = jK V ≫ x' → x ≫ s = 𝟙 _ →
      x' ≫ s = 𝟙 _ → x = x' := by
    intro x x' h hx hx'
    let S : ValuativeCommSq s :=
      { R := V, K := FractionRing V, i₁ := jK V ≫ x, i₂ := 𝟙 _,
        commSq := ⟨by rw [Category.assoc, hx]⟩ }
    have hU : Subsingleton S.commSq.LiftStruct := IsSeparated.valuativeCriterion s S
    exact congrArg CommSq.LiftStruct.l
      (@Subsingleton.elim _ hU (⟨x, rfl, hx⟩ : S.commSq.LiftStruct) (⟨x', h.symm, hx'⟩ : S.commSq.LiftStruct))
  have gen3 : ∀ {A : Scheme.{0}} {U U' U'' : A.Opens} (h1 : U' ≤ U) (h2 : U'' ≤ U') (x : Γ(A, U)ˣ),
      res h2 (res h1 x) = res (h2.trans h1) x := by
    intro A U U' U'' h1 h2 x
    apply Units.ext
    have hm : A.presheaf.map (homOfLE h1).op ≫ A.presheaf.map (homOfLE h2).op =
        A.presheaf.map (homOfLE (h2.trans h1)).op := by
      rw [← Functor.map_comp]
      rfl
    exact congrArg (fun m => m.hom x.val) hm
  have gen5 : ∀ {A : Scheme.{0}} {U1 U2 W : A.Opens} (l : U1 ⊓ U2 ≤ U1) (r : U1 ⊓ U2 ≤ U2)
      (h : W ≤ U1 ⊓ U2) (h1 : W ≤ U1) (h2 : W ≤ U2) (x : Γ(A, U1)ˣ) (y : Γ(A, U2)ˣ),
      res l x = res r y → res h1 x = res h2 y := by
    intro A U1 U2 W l r h h1 h2 x y H
    have H' := congrArg (res h) H
    rw [gen3, gen3] at H'
    exact H'
  have hch : ∀ y : Spec (CommRingCat.of V) ⟶ X, ∃ i : L.ι,
      y.base (IsLocalRing.closedPoint V) ∈ L.U i := by
    intro y
    have hmem : y.base (IsLocalRing.closedPoint V) ∈ ⨆ i, L.U i := by
      rw [hL.cover]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hmem
  choose ich hich using hch
  have htop₁ : LB.wchart L φ₁ (fun k => ich (φ₁ k)) = ⊤ := by
    apply eq_top_of_closedPoint_mem
    show _ ∈ (⋂ k, (φ₁ k).base ⁻¹' (L.U (ich (φ₁ k)) : Set X))
    exact Set.mem_iInter.2 fun k => hich (φ₁ k)
  have htop₂ : LB.wchart L φ₂ (fun k => ich (φ₂ k)) = ⊤ := by
    apply eq_top_of_closedPoint_mem
    show _ ∈ (⋂ k, (φ₂ k).base ⁻¹' (L.U (ich (φ₂ k)) : Set X))
    exact Set.mem_iInter.2 fun k => hich (φ₂ k)
  have hK₁ : (⊤ : (Spec (CommRingCat.of (FractionRing V))).Opens) ≤
      LB.wchart L (fun k => jK V ≫ φ₁ k) (fun k => ich (φ₁ k)) := by
    intro y _
    have hy : (jK V).base y ∈ LB.wchart L φ₁ (fun k => ich (φ₁ k)) := by
      rw [htop₁]
      trivial
    have hy' : (jK V).base y ∈ (⋂ k, (φ₁ k).base ⁻¹' (L.U ((fun k => ich (φ₁ k)) k) : Set X)) := hy
    show y ∈ (⋂ k, (jK V ≫ φ₁ k).base ⁻¹' (L.U ((fun k => ich (φ₁ k)) k) : Set X))
    refine Set.mem_iInter.2 fun k => ?_
    have h1 := Set.mem_iInter.1 hy' k
    simpa using h1
  have hK₂ : (⊤ : (Spec (CommRingCat.of (FractionRing V))).Opens) ≤
      LB.wchart L (fun k => jK V ≫ φ₂ k) (fun k => ich (φ₂ k)) := by
    intro y _
    have hy : (jK V).base y ∈ LB.wchart L φ₂ (fun k => ich (φ₂ k)) := by
      rw [htop₂]
      trivial
    have hy' : (jK V).base y ∈ (⋂ k, (φ₂ k).base ⁻¹' (L.U ((fun k => ich (φ₂ k)) k) : Set X)) := hy
    show y ∈ (⋂ k, (jK V ≫ φ₂ k).base ⁻¹' (L.U ((fun k => ich (φ₂ k)) k) : Set X))
    refine Set.mem_iInter.2 fun k => ?_
    have h1 := Set.mem_iInter.1 hy' k
    simpa using h1
  obtain ⟨m, hm⟩ := exists_genHasVal hϖ L hL φ₂ _ hφ₂ ε₂ t₂ ht₂
  obtain ⟨c1, hc1, u1, h1⟩ := genHasVal_top L φ₁ ε₁ t₁ hn _ htop₁ hK₁
  obtain ⟨c2, hc2, u2, h2⟩ := genHasVal_top L φ₂ ε₂ t₂ hm _ htop₂ hK₂
  have hco := hc (fun k => ich (φ₁ k)) (fun k => ich (φ₂ k))
    (fun a b hab => congrArg ich (sep _ _ hab (hs₁ a) (hs₁ b)))
    (fun a b hab => congrArg ich (sep _ _ hab (hs₂ a) (hs₂ b)))
    (fun a b hab => congrArg ich (sep _ _ hab (hs₁ a) (hs₂ b)))
  have h3 := gen5 _ _ (le_inf hK₁ hK₂) hK₁ hK₂ _ _ hco
  have h4 := congrArg (fun z => (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).hom.hom z.val) h3
  have h5 : c1 * algebraMap V (FractionRing V) (u1 : V) = c2 * algebraMap V (FractionRing V) (u2 : V) :=
    h1.symm.trans (h4.trans h2)
  have hnm : n = m := by
    refine hasVal_unique hϖ (hasVal_mul_unit hc1 u1) ?_
    rw [h5]
    exact hasVal_mul_unit hc2 u2
  rw [hnm]
  exact hm
end ReciprocityTheory.ChartRestriction.G.DVR

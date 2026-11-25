-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.exists_genHasVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:07:21.793584+00:00
-- url     : https://prove2.me/submissions/50dcf477-ae63-47a4-9fc4-c480308996d8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_exists_chart_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_exists_gen_of_local
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_hasVal_of_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen


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
theorem _root_.solution (hϖ : Irreducible ϖ) {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) {Ix : Type} [Fintype Ix]
    (φ : Ix → (Spec (CommRingCat.of V) ⟶ X)) (φ' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ : ∀ k, φ' k = jK V ≫ φ k) (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb L φ' ε)) (ht : t.IsGen) :
    ∃ n, GenHasVal ϖ L φ φ' hφ ε t n := by
  obtain rfl : φ' = fun k => jK V ≫ φ k := funext hφ
  obtain ⟨e, he⟩ := exists_gen_of_local L hL φ ε
  obtain ⟨j₀, htop⟩ := exists_chart_top L hL φ ε
  have hK : (⊤ : (Spec (CommRingCat.of (FractionRing V))).Opens) ≤
      LB.wchart L (fun k => jK V ≫ φ k) j₀ := by
    intro y _
    have hy : (jK V).base y ∈ LB.wchart L φ j₀ := by
      rw [htop]
      trivial
    have hy' : (jK V).base y ∈ (⋂ k, (φ k).base ⁻¹' (L.U (j₀ k) : Set X)) := hy
    show y ∈ (⋂ k, (jK V ≫ φ k).base ⁻¹' (L.U (j₀ k) : Set X))
    refine Set.mem_iInter.2 fun k => ?_
    have h1 := Set.mem_iInter.1 hy' k
    simpa using h1
  have hP := pullGen_isGen L φ ε e he (jK V)
  have gen3 : ∀ {A : Scheme.{0}} {U U' U'' : A.Opens} (h1 : U' ≤ U) (h2 : U'' ≤ U') (x : Γ(A, U)ˣ),
      res h2 (res h1 x) = res (h2.trans h1) x := by
    intro A U U' U'' h1 h2 x
    apply Units.ext
    have hm : A.presheaf.map (homOfLE h1).op ≫ A.presheaf.map (homOfLE h2).op =
        A.presheaf.map (homOfLE (h2.trans h1)).op := by
      rw [← Functor.map_comp]
      rfl
    exact congrArg (fun m => m.hom x.val) hm
  have gen0 : ∀ {A : Scheme.{0}} {U : A.Opens} (h : U ≤ U) (x : Γ(A, U)ˣ), res h x = x := by
    intro A U h x
    apply Units.ext
    show (A.presheaf.map (homOfLE h).op).hom x.val = x.val
    rw [show (homOfLE h).op = 𝟙 (Opposite.op U) from rfl, CategoryTheory.Functor.map_id]
    rfl
  have hle : ∀ j : Ix → L.ι, LB.wchart L (fun k => jK V ≫ φ k) j ≤ LB.wchart L (fun k => jK V ≫ φ k) j₀ :=
    fun j => le_top.trans hK
  have keyA : ∀ {W W0 : (Spec (CommRingCat.of (FractionRing V))).Opens} (hle : W ≤ W0)
      (hl : W ⊓ W0 ≤ W) (hr : W ⊓ W0 ≤ W0)
      (T P : Γ(Spec (CommRingCat.of (FractionRing V)), W)ˣ)
      (T0 P0 : Γ(Spec (CommRingCat.of (FractionRing V)), W0)ˣ)
      (g : Γ(Spec (CommRingCat.of (FractionRing V)), W ⊓ W0)ˣ),
      res hl T = g * res hr T0 → res hl P = g * res hr P0 → T = res hle (T0 / P0) * P := by
    intro W W0 hle hl hr T P T0 P0 g h1 h2
    have h3 : res hl (T / P) = res hr (T0 / P0) := by
      rw [map_div, map_div, h1, h2, mul_div_mul_left_eq_div]
    have h4 := congrArg (res (le_inf le_rfl hle : W ≤ W ⊓ W0)) h3
    rw [gen3, gen3, gen0] at h4
    exact div_eq_iff_eq_mul.1 h4
  set Dt : Γ(Spec (CommRingCat.of (FractionRing V)), ⊤)ˣ :=
    res hK (t.s j₀ / (LB.pullGen L φ ε e (jK V)).s j₀) with hDt
  set c : FractionRing V := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).hom.hom Dt.val with hc
  have hc0 : c ≠ 0 := by
    intro h0
    have hu : IsUnit c := Dt.isUnit.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).hom.hom
    rw [h0] at hu
    exact not_isUnit_zero hu
  obtain ⟨n, hn⟩ := hasVal_of_ne_zero hϖ hc0
  refine ⟨n, e, he, c, hn, fun (j : Ix → L.ι) => ?_⟩
  have hsc : scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c = Dt.val := by
    simp [scal, hc, Scheme.Hom.appTop]
  have hkey := keyA (hle j) inf_le_left inf_le_right (t.s j) ((LB.pullGen L φ ε e (jK V)).s j)
    (t.s j₀) ((LB.pullGen L φ ε e (jK V)).s j₀) _ (ht j j₀) (hP j j₀)
  refine (congrArg Units.val hkey).trans ?_
  have hA : (res (hle j) (t.s j₀ / (LB.pullGen L φ ε e (jK V)).s j₀)).val =
      resTop (LB.wchart L (fun k => jK V ≫ φ k) j) (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) := by
    rw [hsc, hDt]
    exact (congrArg Units.val (gen3 hK (le_top : LB.wchart L (fun k => jK V ≫ φ k) j ≤ ⊤) _)).symm
  exact (Units.val_mul _ _).trans (congrArg₂ (· * ·) hA rfl)
end ReciprocityTheory.ChartRestriction.G.DVR

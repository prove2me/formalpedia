-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.genHasVal_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:13:26.487741+00:00
-- url     : https://prove2.me/submissions/13cab506-1757-4788-aeb0-521fbd7722cc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_genHasVal_units
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
theorem _root_.solution {X : Scheme.{0}} (L : LB X) {Ix : Type} [Fintype Ix]
    (φ : Ix → (Spec (CommRingCat.of V) ⟶ X)) (φ' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ : ∀ k, φ' k = jK V ≫ φ k) (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb L φ' ε)) {n : ℤ}
    (hn : GenHasVal ϖ L φ φ' hφ ε t n) : t.IsGen := by
  obtain rfl : φ' = fun k => jK V ≫ φ k := funext hφ
  obtain ⟨e, he, c, -, hC⟩ := genHasVal_units L φ _ hφ ε t hn
  have hP := pullGen_isGen L φ ε e he (jK V)
  have gen1 : ∀ (W W' : (Spec (CommRingCat.of (FractionRing V))).Opens) (h : W' ≤ W)
      (x : Γ(Spec (CommRingCat.of (FractionRing V)), ⊤)),
      ((Spec (CommRingCat.of (FractionRing V))).presheaf.map (homOfLE h).op).hom (resTop W x) =
        resTop W' x := by
    intro W W' h x
    simp only [resTop]
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  have key : ∀ {Wi Wj : (Spec (CommRingCat.of (FractionRing V))).Opens} (hl : Wi ⊓ Wj ≤ Wi)
      (hr : Wi ⊓ Wj ≤ Wj)
      (Ti Ci Pi : Γ(Spec (CommRingCat.of (FractionRing V)), Wi)ˣ)
      (Tj Cj Pj : Γ(Spec (CommRingCat.of (FractionRing V)), Wj)ˣ)
      (g : Γ(Spec (CommRingCat.of (FractionRing V)), Wi ⊓ Wj)ˣ)
      (x : Γ(Spec (CommRingCat.of (FractionRing V)), ⊤)),
      Ti = Ci * Pi → Tj = Cj * Pj → Ci.val = resTop Wi x → Cj.val = resTop Wj x →
      res hl Pi = g * res hr Pj → res hl Ti = g * res hr Tj := by
    intro Wi Wj hl hr Ti Ci Pi Tj Cj Pj g x h1 h2 h3 h4 h5
    have hCC : res hl Ci = res hr Cj := by
      have e1 : (res hl Ci).val = resTop (Wi ⊓ Wj) x := by
        rw [← gen1 Wi (Wi ⊓ Wj) hl x, ← h3]
        rfl
      have e2 : (res hr Cj).val = resTop (Wi ⊓ Wj) x := by
        rw [← gen1 Wj (Wi ⊓ Wj) hr x, ← h4]
        rfl
      exact Units.ext (e1.trans e2.symm)
    rw [h1, h2, map_mul, map_mul, hCC, h5]
    exact mul_left_comm _ _ _
  intro i j
  obtain ⟨Ci, hCi1, hCi2⟩ := hC i
  obtain ⟨Cj, hCj1, hCj2⟩ := hC j
  exact key _ _ _ Ci _ _ Cj _ _ _ hCi2 hCj2 hCi1 hCj1 (hP i j)
end ReciprocityTheory.ChartRestriction.G.DVR

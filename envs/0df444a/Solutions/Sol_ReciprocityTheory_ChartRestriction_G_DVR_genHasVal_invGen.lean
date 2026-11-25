-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.genHasVal_invGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:30.99237+00:00
-- url     : https://prove2.me/submissions/cd15cc83-a533-4f6c-9351-16eb2bb02fb4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen


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
theorem _root_.solution {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) {Ix : Type} [Fintype Ix]
    (φ : Ix → (Spec (CommRingCat.of V) ⟶ X)) (φ' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ : ∀ k, φ' k = jK V ≫ φ k) (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb L φ' ε)) {n : ℤ}
    (hn : GenHasVal ϖ L φ φ' hφ ε t n) :
    GenHasVal ϖ L φ φ' hφ (fun k => - ε k) (LB.invGen L φ' ε t) (-n) := by
  obtain ⟨e, he, c, ⟨u, hu⟩, hj⟩ := hn
  refine ⟨LB.invGen L φ ε e, invGen_isGen L φ ε e he, c⁻¹, ⟨u⁻¹, ?_⟩, fun (j : Ix → L.ι) => ?_⟩
  · rw [hu, mul_inv, zpow_neg, map_units_inv]
  · have hT := hj j
    have hxy : resTop (LB.wchart L φ' j) (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) *
        resTop (LB.wchart L φ' j) (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c⁻¹) = 1 := by
      by_cases hc : c = 0
      · have h0 : (t.s j).val = 0 := by
          have hs0 : scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) (0 : FractionRing V) = 0 := by
            simp only [scal, map_zero]
          have hr0 : resTop (LB.wchart L φ' j)
              (0 : Γ(Spec (CommRingCat.of (FractionRing V)), ⊤)) = 0 := by
            simp only [resTop, map_zero]
          rw [hT, hc, hs0, hr0]
          exact zero_mul _
        have hu0 := (t.s j).isUnit
        rw [h0] at hu0
        exact eq_of_zero_eq_one (isUnit_zero_iff.1 hu0) _ _
      · simp only [resTop, scal, ← map_mul, mul_inv_cancel₀ hc, map_one]
    change ((t.s j)⁻¹).val = _
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hT, show (LB.invGen L φ ε e).s j = (e.s j)⁻¹ from rfl]
    have hRR : (res (wchart_le_preimage L (jK V) φ φ' hφ j) (pullU (jK V) (LB.wchart L φ j) (e.s j))).val *
        (res (wchart_le_preimage L (jK V) φ φ' hφ j) (pullU (jK V) (LB.wchart L φ j) (e.s j)⁻¹)).val = 1 := by
      have gen : ∀ {A B : Scheme.{0}} (f : A ⟶ B) (U : B.Opens) (W : A.Opens) (hW : W ≤ f ⁻¹ᵁ U)
          (x : Γ(B, U)ˣ), (res hW (pullU f U x)).val * (res hW (pullU f U x⁻¹)).val = 1 := by
        intro A B f U W hW x
        rw [map_inv, map_inv]
        exact Units.mul_inv _
      exact gen _ _ _ _ (e.s j)
    have key : ∀ (x y r r' : Γ(Spec (CommRingCat.of (FractionRing V)), LB.wchart L φ' j)),
        x * y = 1 → r * r' = 1 → x * r * (y * r') = 1 := by
      intro x y r r' h1 h2
      calc x * r * (y * r') = (x * y) * (r * r') := by ring
        _ = 1 := by rw [h1, h2, one_mul]
    exact key _ _ _ _ hxy hRR
end ReciprocityTheory.ChartRestriction.G.DVR

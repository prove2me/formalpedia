-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.genHasVal_units
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:25.031627+00:00
-- url     : https://prove2.me/submissions/505252e1-bf19-466a-8ab9-15c16323ebf4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC

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
    (hn : GenHasVal ϖ L φ φ' hφ ε t n) :
    ∃ e : LB.Gen (LB.LinComb L φ ε), e.IsGen ∧ ∃ c : FractionRing V, HasVal ϖ c n ∧
      ∀ j : Ix → L.ι, ∃ C : Γ(Spec (CommRingCat.of (FractionRing V)), LB.wchart L φ' j)ˣ,
        C.val = resTop _ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) ∧
        (t.s j : Γ(Spec (CommRingCat.of (FractionRing V)), LB.wchart L φ' j)ˣ) =
          C * res (wchart_le_preimage L (jK V) φ φ' hφ j) (pullU (jK V) _ (e.s j)) := by
  obtain ⟨e, he, c, hc, h⟩ := hn
  refine ⟨e, he, c, hc, fun j => ?_⟩
  obtain ⟨y, hy⟩ : ∃ y : Γ(Spec (CommRingCat.of (FractionRing V)), LB.wchart L φ' j)ˣ, y = t.s j :=
    ⟨_, rfl⟩
  have hj := h j
  rw [← hy] at hj ⊢
  refine ⟨y * (res (wchart_le_preimage L (jK V) φ φ' hφ j) (pullU (jK V) _ (e.s j)))⁻¹, ?_, ?_⟩
  · rw [Units.val_mul, hj]
    first
      | exact Units.mul_inv_cancel_right _ _
      | simp
  · exact (inv_mul_cancel_right _ _).symm
end ReciprocityTheory.ChartRestriction.G.DVR

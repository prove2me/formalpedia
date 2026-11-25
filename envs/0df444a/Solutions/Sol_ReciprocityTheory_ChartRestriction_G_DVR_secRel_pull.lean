-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.secRel_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:50:44.195539+00:00
-- url     : https://prove2.me/submissions/d1c1c16a-03bb-4e1f-b169-70add37fdebd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpIdentRestrict
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RsAppPullGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs


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
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {X Y Y' Z : Scheme.{0}} (L : LB X) {K₁ K₂ K₃ K K' : Type} [Fintype K₁] [Fintype K₂] [Fintype K₃]
  [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (φ₁ : K₁ → (Y' ⟶ X)) (ε₁ : K₁ → ℤ) (s₁ : LB.Sec (LB.LinComb L φ₁ ε₁))
    (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) (s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)) (h : Y' ⟶ Y)
    (φ₃ : K₃ → (Y' ⟶ X)) (ε₃ : K₃ → ℤ) (u : LB.Gen (LB.LinComb L φ₃ ε₃))
    (hrel : GeneratorPullback.SecRel L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h φ₃ ε₃ u)
    (j₁ : K₁ → L.ι) (j₂ : K₂ → L.ι) (j₃ : K₃ → L.ι)
    (hcoh : LB.Coh L (Sum.elim φ₁ (Sum.elim (fun k => h ≫ φ₂ k) φ₃)) (Sum.elim j₁ (Sum.elim j₂ j₃)))
    (q : Z ⟶ Y') {O : Z.Opens}
    (h₁ : O ≤ q ⁻¹ᵁ LB.wchart L φ₁ j₁) (h₂ : O ≤ (q ≫ h) ⁻¹ᵁ LB.wchart L φ₂ j₂)
    (h₃ : O ≤ q ⁻¹ᵁ LB.wchart L φ₃ j₃) :
    rs h₁ ((q.app _).hom (s₁.f j₁)) =
      rs h₂ (((q ≫ h).app _).hom (s₂.f j₂)) * rs h₃ ((q.app _).hom (u.s j₃).val) := by
  have hOb : O ≤ q ⁻¹ᵁ (LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ⊓ LB.wchart L φ₃ j₃) := by
    intro z hz
    refine ⟨⟨h₁ hz, Set.mem_iInter.2 fun k => ?_⟩, h₃ hz⟩
    have := Set.mem_iInter.1 (h₂ hz) k
    simpa [Scheme.Hom.comp_apply] using this
  have key : rs (inf_le_left.trans inf_le_left : _ ≤ LB.wchart L φ₁ j₁) (s₁.f j₁) =
      rs ((inf_le_left.trans inf_le_right).trans (wchart_comp_le φ₂ h j₂)) ((h.app _).hom (s₂.f j₂)) *
      rs (inf_le_right : _ ≤ LB.wchart L φ₃ j₃) (u.s j₃).val := hrel j₁ j₂ j₃ hcoh
  have ha : LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ⊓ LB.wchart L φ₃ j₃ ≤ LB.wchart L φ₁ j₁ :=
    inf_le_left.trans inf_le_left
  have hb : LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ⊓ LB.wchart L φ₃ j₃ ≤
      h ⁻¹ᵁ LB.wchart L φ₂ j₂ := (inf_le_left.trans inf_le_right).trans (wchart_comp_le φ₂ h j₂)
  have hc : LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ⊓ LB.wchart L φ₃ j₃ ≤
      LB.wchart L φ₃ j₃ := inf_le_right
  have e1 : rs hOb ((q.app _).hom (rs ha (s₁.f j₁))) = rs h₁ ((q.app _).hom (s₁.f j₁)) :=
    (congrArg (rs hOb) (app_rs q ha (s₁.f j₁))).trans (rs_rs _ _ _)
  have e2 : rs hOb ((q.app _).hom (rs hb ((h.app _).hom (s₂.f j₂)))) =
      rs h₂ (((q ≫ h).app _).hom (s₂.f j₂)) := by
    rw [app_rs, rs_rs]
    rfl
  have e3 : rs hOb ((q.app _).hom (rs hc (u.s j₃).val)) = rs h₃ ((q.app _).hom (u.s j₃).val) :=
    (congrArg (rs hOb) (app_rs q hc (u.s j₃).val)).trans (rs_rs _ _ _)
  rw [← e1, ← e2, ← e3, ← rs_mul, ← map_mul]
  exact congrArg (fun x => rs hOb ((q.app _).hom x)) key
end ReciprocityTheory.ChartRestriction.G.DVR

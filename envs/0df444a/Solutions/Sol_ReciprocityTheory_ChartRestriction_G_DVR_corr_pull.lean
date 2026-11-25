-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.corr_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:32:55.482374+00:00
-- url     : https://prove2.me/submissions/70b6a913-2a35-4908-82a9-ca4ef3af00bb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpIdentRestrict
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RsAppPullGen
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
theorem _root_.solution (φ : K → (Y' ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y' ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (hc : LB.Gen.Corr L φ ε φ' ε' t t') (j : K → L.ι) (j' : K' → L.ι) (hj : LB.Coh L φ j)
    (hj' : LB.Coh L φ' j') (hjj : ∀ k k', φ k = φ' k' → j k = j' k')
    (q : Z ⟶ Y') {O : Z.Opens} (h₁ : O ≤ q ⁻¹ᵁ LB.wchart L φ j) (h₂ : O ≤ q ⁻¹ᵁ LB.wchart L φ' j') :
    rs h₁ ((q.app _).hom (t.s j).val) = rs h₂ ((q.app _).hom (t'.s j').val) := by
  have hO : O ≤ q ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ' j') := fun z hz => ⟨h₁ hz, h₂ hz⟩
  have key : rs (inf_le_left : _ ≤ LB.wchart L φ j) (t.s j).val =
      rs (inf_le_right : _ ≤ LB.wchart L φ' j') (t'.s j').val := by
    exact congrArg Units.val (hc j j' hj hj' hjj)
  have e1 : rs hO ((q.app _).hom (rs (inf_le_left : _ ≤ LB.wchart L φ j) (t.s j).val)) =
      rs h₁ ((q.app _).hom (t.s j).val) :=
    (congrArg (rs hO) (app_rs q (inf_le_left : _ ≤ LB.wchart L φ j) (t.s j).val)).trans (rs_rs _ _ _)
  have e2 : rs hO ((q.app _).hom (rs (inf_le_right : _ ≤ LB.wchart L φ' j') (t'.s j').val)) =
      rs h₂ ((q.app _).hom (t'.s j').val) :=
    (congrArg (rs hO) (app_rs q (inf_le_right : _ ≤ LB.wchart L φ' j') (t'.s j').val)).trans (rs_rs _ _ _)
  rw [← e1, ← e2]
  exact congrArg (fun x => rs hO ((q.app _).hom x)) key
end ReciprocityTheory.ChartRestriction.G.DVR

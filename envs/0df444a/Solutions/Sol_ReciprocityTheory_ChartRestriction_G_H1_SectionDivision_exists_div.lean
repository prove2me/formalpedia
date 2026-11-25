-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.SectionDivision.exists_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:07:31.801106+00:00
-- url     : https://prove2.me/submissions/94863022-8e40-427d-b873-276e57291446

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionDivision
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionDivision_exists_section

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.SectionDivision
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
namespace ReciprocityTheory.ChartRestriction.G.H1.SectionDivision
theorem _root_.solution (hmul : MulNSt) {k : Type} [Field k] [IsAlgClosed k]
    (P : PolAV (Spec (CommRingCat.of k))) (a₀ : baseOver (Spec (CommRingCat.of k)) ⟶ P.A) (r : ℕ)
    (hr : 1 ≤ r) : ∃ b : baseOver (Spec (CommRingCat.of k)) ⟶ P.A, b ^ r = a₀ := by
  obtain ⟨hfin, -, hsurj, -, -⟩ := hmul (Spec (CommRingCat.of k)) P r hr
  obtain ⟨t, ht⟩ := exists_section (pullback.snd (mulA P.A r).left a₀.left)
  have hb' : (t ≫ pullback.fst (mulA P.A r).left a₀.left) ≫ (mulA P.A r).left = a₀.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht, Category.id_comp]
  have hw : (t ≫ pullback.fst (mulA P.A r).left a₀.left) ≫ P.A.hom = (baseOver (Spec (CommRingCat.of k))).hom := by
    rw [← Over.w (mulA P.A r), ← Category.assoc, hb', Over.w a₀]
  refine ⟨Over.homMk _ hw, ?_⟩
  have e : ∀ b : baseOver (Spec (CommRingCat.of k)) ⟶ P.A, b ^ r = b ≫ mulA P.A r := fun b =>
    (congrArg (· ^ r) (Category.comp_id b).symm).trans (MonObj.comp_pow (𝟙 P.A) r b).symm
  rw [e]
  exact Over.OverMorphism.ext hb'
end ReciprocityTheory.ChartRestriction.G.H1.SectionDivision

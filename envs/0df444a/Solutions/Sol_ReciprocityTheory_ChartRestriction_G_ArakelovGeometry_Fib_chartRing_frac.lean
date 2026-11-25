-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.chartRing_frac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:38:07.440831+00:00
-- url     : https://prove2.me/submissions/bdd45cd3-340b-4268-9b8f-793dbc356883

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_coord_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_coord_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
theorem _root_.solution (y : Fin (D + 1) → Ω) (hfree : coordIdeal ℤ y = ⊥) :
    IsFractionRing (chartRing y) (fnField y) := by
  have hl : y 0 ≠ 0 := coord_ne_zero y hfree 0
  refine IsFractionRing.of_field _ _ fun z => ?_
  have hinj : Function.Injective (algebraMap (chartRing y) Ω) := by
    intro a b hab
    exact Subtype.val_injective (Subtype.val_injective hab)
  let F : Subfield Ω := (IsFractionRing.lift (K := FractionRing (chartRing y)) hinj).fieldRange
  have hgen : ∀ i, y i / y 0 ∈ F := by
    intro i
    by_cases hi : i = 0
    · subst hi; rw [div_self hl]; exact F.one_mem
    · refine ⟨algebraMap (chartRing y) (FractionRing (chartRing y))
        ⟨chartGen y ⟨i, hi⟩, Algebra.subset_adjoin ⟨_, rfl⟩⟩, ?_⟩
      rw [IsFractionRing.lift_algebraMap hinj]
      rfl
  have hle : (fnField y).toSubfield ≤ F := by
    unfold fnField
    refine IntermediateField.adjoin_le_subfield ℚ _ ?_ ?_
    · rintro _ ⟨q, rfl⟩
      rw [eq_ratCast]
      exact SubfieldClass.ratCast_mem F q
    · rintro _ ⟨i, j, rfl⟩
      have : y i / y j = (y i / y 0) / (y j / y 0) := by
        rw [div_div_div_cancel_right₀ hl]
      change y i / y j ∈ F
      rw [this]
      exact F.div_mem (hgen i) (hgen j)
  obtain ⟨w, hw⟩ := hle z.2
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := chartRing y) w
  refine ⟨a, b, Subtype.val_injective ?_⟩
  rw [map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap] at hw
  rw [← hw]
  exact (map_div₀ (fnField y).val _ _).symm
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

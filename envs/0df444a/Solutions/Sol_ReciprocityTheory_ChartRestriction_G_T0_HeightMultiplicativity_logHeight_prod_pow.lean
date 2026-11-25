-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity.logHeight_prod_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:50:49.083242+00:00
-- url     : https://prove2.me/submissions/b2adbc78-3948-47b6-befe-b3827093a039

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HeightMultiplicativity_multi_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HeightMultiplicativity_multi_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HeightMultiplicativity_multi_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HeightMultiplicativity_h0_pow_of_isMultiHomogeneous
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_gauss_height_additivity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_zero



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
open MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
theorem _root_.solution {B n : ℕ} (hn : 0 < n) {α : Type*} (s : Finset α) (e : α → Fin B → ℕ)
    (f : α → MvPolynomial (Fin B × Fin n) K) (k : α → ℕ)
    (hf0 : ∀ i ∈ s, f i ≠ 0) (hf : ∀ i ∈ s, IsMultiHomogeneous (e i) (f i)) :
    h0 (∏ i ∈ s, f i ^ k i) = ∑ i ∈ s, (k i : ℝ) * h0 (f i) := by
  classical
  have h1 : h0 (1 : MvPolynomial (Fin B × Fin n) K) = 0 := by
    have e := (gauss_height_additivity K B n 0 0 1 1 hn one_ne_zero one_ne_zero multi_one multi_one).1
    rw [one_mul] at e
    linarith
  induction s using Finset.induction_on with
  | empty => simp [h1]
  | insert i s hi ih =>
    have hf0' : ∀ j ∈ s, f j ≠ 0 := fun j hj => hf0 j (Finset.mem_insert_of_mem hj)
    have hf' : ∀ j ∈ s, IsMultiHomogeneous (e j) (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hP0 : ∏ j ∈ s, f j ^ k j ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j hj => pow_ne_zero _ (hf0' j hj)
    have hPm : IsMultiHomogeneous (∑ j ∈ s, k j • e j) (∏ j ∈ s, f j ^ k j) :=
      multi_prod s (fun j => k j • e j) (fun j => f j ^ k j) fun j hj => multi_pow (hf' j hj) (k j)
    have hi0 := hf0 i (Finset.mem_insert_self i s)
    have him := hf i (Finset.mem_insert_self i s)
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      (gauss_height_additivity K B n _ _ _ _ hn (pow_ne_zero _ hi0) hP0 (multi_pow him (k i)) hPm).1,
      h0_pow_of_isMultiHomogeneous hn hi0 him, ih hf0' hf']
end ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

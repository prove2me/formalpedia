-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity.h0_pow_of_isMultiHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:39:14.388877+00:00
-- url     : https://prove2.me/submissions/05940a2a-be24-4a84-ab09-2225b65127dc

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HeightMultiplicativity_multi_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HeightMultiplicativity_multi_pow
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
theorem _root_.solution {B n : ℕ} (hn : 0 < n) {a : Fin B → ℕ} {f : MvPolynomial (Fin B × Fin n) K}
    (hf0 : f ≠ 0) (hf : IsMultiHomogeneous a f) (k : ℕ) : h0 (f ^ k) = k * h0 f := by
  have h1 : h0 (1 : MvPolynomial (Fin B × Fin n) K) = 0 := by
    have e := (gauss_height_additivity K B n 0 0 1 1 hn one_ne_zero one_ne_zero multi_one multi_one).1
    rw [one_mul] at e
    linarith
  induction k with
  | zero => simp [h1]
  | succ k ih =>
    rw [pow_succ, (gauss_height_additivity K B n _ a (f ^ k) f hn (pow_ne_zero _ hf0) hf0 (multi_pow hf k) hf).1, ih]
    push_cast
    ring
end ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

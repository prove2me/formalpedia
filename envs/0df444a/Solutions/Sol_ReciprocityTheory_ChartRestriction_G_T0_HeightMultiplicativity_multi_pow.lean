-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity.multi_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:56:49.696564+00:00
-- url     : https://prove2.me/submissions/0b07eff7-0718-473b-aa33-3da93c207e0f

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HeightMultiplicativity_multi_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HeightMultiplicativity_multi_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_zero
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
namespace ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
theorem _root_.solution {R : Type*} [CommSemiring R] {B n : ℕ} {a : Fin B → ℕ}
    {f : MvPolynomial (Fin B × Fin n) R} (hf : IsMultiHomogeneous a f) (k : ℕ) :
    IsMultiHomogeneous (k • a) (f ^ k) := by
  induction k with
  | zero => simpa using (multi_one : IsMultiHomogeneous (0 : Fin B → ℕ) (1 : MvPolynomial (Fin B × Fin n) R))
  | succ k ih =>
    rw [pow_succ, succ_nsmul]
    exact multi_mul ih hf
end ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

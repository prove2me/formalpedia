-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.uniformizer_abs_eq_inv_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:54:46.461989+00:00
-- url     : https://prove2.me/submissions/6f4392e0-d635-42a5-a7bc-0eba8c92b0ae

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscBDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OpIsDVR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintIntOfBounds
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogHeightDivMultihomogeneous
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_unif_mem
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (la : HeightOneSpectrum (𝓞 K)) :
    FinitePlace.mk la ((Data.unif la : 𝓞 K) : K) = ((Ideal.absNorm la.asIdeal : ℕ) : ℝ)⁻¹ := by
  obtain ⟨h1, h2⟩ := unif_mem la
  have a1 : la.intValuation (Data.unif la) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (la.intValuation_le_pow_iff_mem _ 1).2 (by rw [pow_one]; exact h1)
  have a2 : ¬ la.intValuation (Data.unif la) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => h2 ((la.intValuation_le_pow_iff_mem _ 2).1 h)
  have hne : la.intValuation (Data.unif la) ≠ 0 := by
    intro h0; apply a2; rw [h0]; exact zero_le
  have hv : la.intValuation (Data.unif la) = WithZero.exp (-1 : ℤ) := by
    rw [← WithZero.exp_log hne] at a1 a2 ⊢
    rw [WithZero.exp_le_exp] at a1 a2
    congr 1
    push_cast at a1 a2
    omega
  rw [FinitePlace.mk_apply]
  have := FinitePlace.norm_embedding_int (K := K) (v := la) (Data.unif la)
  simp only [RingOfIntegers.coe_eq_algebraMap] at this ⊢
  rw [this, hv]
  simp [WithZeroMulInt.toNNReal_neg_apply, WithZero.exp]
end ReciprocityTheory.ChartRestriction.G.T0

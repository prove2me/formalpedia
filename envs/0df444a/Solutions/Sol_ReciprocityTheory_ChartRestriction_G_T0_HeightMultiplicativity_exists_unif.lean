-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity.exists_unif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:23:54.55481+00:00
-- url     : https://prove2.me/submissions/868dd2c9-3fe0-4f5c-bced-28cd49aee629

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDA
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
open MvPolynomial ReciprocityTheory.MultiplicativeHeights NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
theorem _root_.solution (la : HeightOneSpectrum (𝓞 K)) :
    ∃ ϖ : 𝓞 K, ϖ ∈ la.asIdeal ∧ ϖ ∉ la.asIdeal ^ 2 ∧
      FinitePlace.mk la (ϖ : K) = ((Ideal.absNorm la.asIdeal : ℕ) : ℝ)⁻¹ := by
  obtain ⟨π, hπ⟩ := la.intValuation_exists_uniformizer
  refine ⟨π, ?_, ?_, ?_⟩
  · have h1 := (la.intValuation_le_pow_iff_mem π 1).1 (by rw [hπ]; simp)
    simpa using h1
  · intro h2
    have h3 := (la.intValuation_le_pow_iff_mem π 2).2 h2
    rw [hπ, WithZero.exp_le_exp] at h3
    norm_num at h3
  · rw [FinitePlace.mk_apply, show (π : K) = algebraMap (𝓞 K) K π from rfl, FinitePlace.norm_def_int K la π, hπ,
      WithZeroMulInt.toNNReal_neg_apply _ (WithZero.exp_ne_zero)]
    push_cast
    exact zpow_neg_one _
end ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

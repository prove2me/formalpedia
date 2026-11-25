-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity.log_gauss_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:46:10.837215+00:00
-- url     : https://prove2.me/submissions/cd3c1851-1d6d-43d2-afc7-151bf9819ead

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HeightMultiplicativity_gaussAbs_C
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HeightMultiplicativity_gaussAbs_prim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_abs_mul
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_abs_pos_of_ne_zero
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
theorem _root_.solution {σ : Type*} [Fintype σ] (la : HeightOneSpectrum (𝓞 K)) (ϖ : 𝓞 K)
    (hϖ : FinitePlace.mk la (ϖ : K) = ((Ideal.absNorm la.asIdeal : ℕ) : ℝ)⁻¹)
    (A B : MvPolynomial σ K) (hA : A ≠ 0) (hB : B ≠ 0) (X S : MvPolynomial σ (𝓞 K))
    (hX : X ∉ Ideal.map (C : 𝓞 K →+* MvPolynomial σ (𝓞 K)) la.asIdeal)
    (hS : S ∉ Ideal.map (C : 𝓞 K →+* MvPolynomial σ (𝓞 K)) la.asIdeal) (m : ℕ)
    (h : A * MvPolynomial.map (algebraMap (𝓞 K) K) S =
      C ((ϖ : K) ^ m) * MvPolynomial.map (algebraMap (𝓞 K) K) X * B) :
    Real.log (gaussAbs (FinitePlace.mk la) A) - Real.log (gaussAbs (FinitePlace.mk la) B) =
      -((m : ℝ) * Real.log (Ideal.absNorm la.asIdeal : ℕ)) := by
  set w := FinitePlace.mk la
  have hS0 : MvPolynomial.map (algebraMap (𝓞 K) K) S ≠ 0 := by
    intro h0; have := gaussAbs_prim la S hS; rw [h0] at this; simp [gaussAbs] at this
  have hX0 : MvPolynomial.map (algebraMap (𝓞 K) K) X ≠ 0 := by
    intro h0; have := gaussAbs_prim la X hX; rw [h0] at this; simp [gaussAbs] at this
  have hN : (0 : ℝ) < ((Ideal.absNorm la.asIdeal : ℕ) : ℝ) := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm la
    exact_mod_cast (zero_lt_one.trans this)
  have hϖ0 : (ϖ : K) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hϖ; exact (inv_pos.2 hN).ne' hϖ.symm
  have hC0 : (C ((ϖ : K) ^ m) : MvPolynomial σ K) ≠ 0 := by
    rw [Ne, C_eq_zero]; exact pow_ne_zero _ hϖ0
  have key := congrArg (gaussAbs w) h
  rw [gauss_abs_mul w _ _ hA hS0, gauss_abs_mul w _ _ (mul_ne_zero hC0 hX0) hB,
    gauss_abs_mul w _ _ hC0 hX0, gaussAbs_prim la S hS, gaussAbs_prim la X hX, gaussAbs_C,
    map_pow, hϖ, mul_one, mul_one] at key
  have hA' := gauss_abs_pos_of_ne_zero w A hA
  have hB' := gauss_abs_pos_of_ne_zero w B hB
  rw [key, Real.log_mul (pow_ne_zero _ (inv_pos.2 hN).ne') hB'.ne', Real.log_pow, Real.log_inv]
  ring
end ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

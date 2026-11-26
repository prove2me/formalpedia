-- Prove2me | solution 1 for P2M_Malliavin_compLp___indicatorConstLp_d787aaa6adc5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:28:03.496007+00:00
-- url     : https://prove2.me/submissions/0dcb6933-16cd-49be-97ba-86d32f1c2cab

import Definitions.Def_Malliavin_WienerIntegral
import Definitions.Def_Malliavin_FubiniLift
import Definitions.Def_Malliavin_MalliavinDerivative
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_TimeDerivative
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {Ω E F : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
namespace Malliavin
theorem _root_.solution (L : E →ₗᵢ[ℝ] F) {A : Set Ω} (hA : MeasurableSet A)
    (hμA : μ A ≠ ∞) (c : E) :
    compLpₗᵢ L (indicatorConstLp 2 hA hμA c) = indicatorConstLp 2 hA hμA (L c) := by
  apply Lp.ext
  filter_upwards [coeFn_compLpₗᵢ L (indicatorConstLp 2 hA hμA c),
    indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hμA) (c := c),
    indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hμA) (c := L c)] with ω h1 h2 h3
  rw [h1, h2, h3]
  by_cases hω : ω ∈ A <;> simp [hω]
end Malliavin

-- Prove2me | solution 1 for P2M_Malliavin_compLp___boundedSMul_3f896ab5bcad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:27:57.293875+00:00
-- url     : https://prove2.me/submissions/8ac37d37-56a5-4ae3-b936-d5457abebcea

import Definitions.Def_Malliavin_WienerIntegral
import Definitions.Def_Malliavin_FubiniLift
import Definitions.Def_Malliavin_MalliavinDerivative
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_TimeDerivative
import Theorems.Thm_Malliavin_coeFn_boundedSMul


set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {Ω E F : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
namespace Malliavin
theorem _root_.solution (L : E →ₗᵢ[ℝ] F) {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ)
    {C : ℝ} (hC : ∀ x, |G x| ≤ C) (f : Lp E 2 μ) :
    compLpₗᵢ L (boundedSMul hG hC f) = boundedSMul hG hC (compLpₗᵢ L f) := by
  apply Lp.ext
  filter_upwards [coeFn_compLpₗᵢ L (boundedSMul hG hC f), coeFn_boundedSMul hG hC f,
    coeFn_boundedSMul hG hC (compLpₗᵢ L f), coeFn_compLpₗᵢ L f] with ω h1 h2 h3 h4
  rw [h1, h2, h3, h4, map_smul]
end Malliavin

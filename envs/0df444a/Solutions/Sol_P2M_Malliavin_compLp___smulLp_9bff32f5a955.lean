-- Prove2me | solution 1 for P2M_Malliavin_compLp___smulLp_9bff32f5a955
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:28:12.469796+00:00
-- url     : https://prove2.me/submissions/8033446b-4bb4-4b0f-b788-9993f4edb032

import Definitions.Def_Malliavin_WienerIntegral
import Definitions.Def_Malliavin_FubiniLift
import Definitions.Def_Malliavin_MalliavinDerivative
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_TimeDerivative
import Theorems.Thm_Malliavin_coeFn_smulLp


set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {Ω E F : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
namespace Malliavin
theorem _root_.solution (L : E →ₗᵢ[ℝ] F) (e : E) (G : Lp ℝ 2 μ) :
    compLpₗᵢ L (smulLp e G) = smulLp (L e) G := by
  apply Lp.ext
  filter_upwards [coeFn_compLpₗᵢ L (smulLp e G), coeFn_smulLp e G, coeFn_smulLp (L e) G]
    with ω h1 h2 h3
  rw [h1, h2, h3, map_smul]
end Malliavin

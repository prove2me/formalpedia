-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_adicAbv_of_intValuation_eq_ca2fe8961340
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:24:10.594146+00:00
-- url     : https://prove2.me/submissions/56c2c2a0-cbdb-4f19-8ff1-8ffded882629

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGaussDVR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain WithZero
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K}
    (ha : v.intValuation a = exp (-1 : ℤ)) :
    NumberField.HeightOneSpectrum.adicAbv K v (algebraMap (𝓞 K) K a) =
      (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def, HeightOneSpectrum.valuation_of_algebraMap, ha,
    WithZeroMulInt.toNNReal_neg_apply _ exp_ne_zero]
  have h1 : Multiplicative.toAdd (unzero (exp_ne_zero (a := (-1 : ℤ)))) = -1 := rfl
  rw [h1, zpow_neg_one, NNReal.coe_inv, NNReal.coe_natCast]
end GroundTheory.Heights₂.Heights.Vertical

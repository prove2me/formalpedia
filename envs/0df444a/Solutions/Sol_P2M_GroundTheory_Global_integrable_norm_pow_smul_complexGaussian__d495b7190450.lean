-- Prove2me | solution 1 for P2M_GroundTheory_Global_integrable_norm_pow_smul_complexGaussian__d495b7190450
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:27:35.29727+00:00
-- url     : https://prove2.me/submissions/eed46cf0-b801-4a22-8fb7-2830d793504b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Gaussian
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplex
import Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
import Theorems.Thm_GroundTheory_Global_integrable_norm_pow_smul_complexGaussian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.traceFormℂ_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Complex MeasureTheory Set Real ComplexConjugate
open scoped FourierTransform ENNReal
noncomputable section
namespace GroundTheory.Global
theorem _root_.solution (m : ℤ) (k : ℕ) :
    Integrable (fun z : ℂ ↦ (‖z‖ ^ k : ℝ) • complexGaussian m z) complexPlaceMeasure :=
  (integrable_norm_pow_smul_complexGaussian m k).smul_measure (by simp)
end GroundTheory.Global

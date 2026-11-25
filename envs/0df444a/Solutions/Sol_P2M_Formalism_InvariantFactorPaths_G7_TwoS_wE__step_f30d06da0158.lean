-- Prove2me | solution 1 for P2M_Formalism_InvariantFactorPaths_G7_TwoS_wE__step_f30d06da0158
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:45:29.10865+00:00
-- url     : https://prove2.me/submissions/b29d71aa-73dc-414d-978a-273a3a899ace

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_pinv_nonneg
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_finsum_le_of
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integralSubstV
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_one
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp low_subst_of_low norm_finsum_le_of)
open Formalism.FG.SolveVAux (Low low_pow low_one_iff)
open Formalism.FG.IntegralSubstitution (integral_mul integral_pow integral_one integralSubstV)
open Formalism.InvariantFactorPaths.G7.TwoS
variable {ν : ℕ}
variable {K : Type}
variable [NormedField K] [IsUltrametricDist K]
namespace Formalism.InvariantFactorPaths.G7.TwoS
theorem _root_.solution {p : ℕ} (hp : p ≠ 0) {u : ZMod (2 * ν) → K}
    (hu2 : ∀ s, ‖u (s + 1) - u s ^ p‖ ≤ (p : ℝ)⁻¹) (k : ℕ) (s : ZMod (2 * ν)) :
    ‖wE u k s ^ p - wE' u k s‖ ≤ (p : ℝ)⁻¹ := by
  unfold wE wE'
  split_ifs
  · rw [norm_sub_rev]; exact hu2 s
  · rw [zero_pow hp, sub_zero, norm_zero]; exact pinv_nonneg p
end Formalism.InvariantFactorPaths.G7.TwoS

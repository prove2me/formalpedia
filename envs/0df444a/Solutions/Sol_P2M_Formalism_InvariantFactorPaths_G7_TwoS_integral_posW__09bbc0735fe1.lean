-- Prove2me | solution 1 for P2M_Formalism_InvariantFactorPaths_G7_TwoS_integral_posW__09bbc0735fe1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:45:25.785059+00:00
-- url     : https://prove2.me/submissions/1c63a072-6249-4eb1-9067-2fb9ceafb90b

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_sPos
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
variable {r0 r1 : ℕ}
namespace Formalism.InvariantFactorPaths.G7.TwoS
theorem _root_.solution [NeZero ν] (p : ℕ) {w : ZMod (2 * ν) → K} (hw : ∀ s, ‖w s‖ ≤ 1)
    (ab : Fin r0 × Fin r1) : Integral (posW' p w ab) :=
  integral_sum _ _ fun s _ =>
    integral_mul (integral_C (hw s)) (integral_pow (integral_sPos p s ab) p)
end Formalism.InvariantFactorPaths.G7.TwoS

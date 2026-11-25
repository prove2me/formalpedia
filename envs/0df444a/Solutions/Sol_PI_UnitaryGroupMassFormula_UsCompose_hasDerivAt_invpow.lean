-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.hasDerivAt_invpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:47:21.804823+00:00
-- url     : https://prove2.me/submissions/0f2b6e91-5f4e-4a59-b4ad-cb1fe425f1ba

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_HasDerivAtInvpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCompose
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.UnitaryGroupMassFormula.UsCompose
theorem _root_.solution {c : ℝ → ℂ} {c' : ℂ} (hc : HasDerivAt c c' 0) (h0 : c 0 ≠ 0) (a : ℕ) :
    HasDerivAt (fun t => (c t)⁻¹ ^ a) (-(a : ℂ) * c' * (c 0)⁻¹ ^ (a + 1)) 0 := by
  have h2 := ((hasDerivAt_inv h0).pow a).comp (0 : ℝ) hc
  have hf : (fun t => (c t)⁻¹ ^ a) = ((fun y => y⁻¹) ^ a) ∘ c := by
    funext t; simp [Function.comp, Pi.pow_apply]
  rw [hf]
  refine h2.congr_deriv ?_
  rcases a with _ | a
  · simp
  · simp only [Nat.add_sub_cancel, inv_pow]
    field_simp
    ring
end PI.UnitaryGroupMassFormula.UsCompose

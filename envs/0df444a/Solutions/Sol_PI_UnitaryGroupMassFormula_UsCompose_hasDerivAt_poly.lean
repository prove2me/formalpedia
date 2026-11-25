-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.hasDerivAt_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:06:32.911735+00:00
-- url     : https://prove2.me/submissions/0a60ac2b-19f0-4594-9966-e826ad4b0b56

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_HasDerivAtInvpow
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_hasDerivAt_eval
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_crv_var

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
theorem _root_.solution {k r : ℕ} (X g : Mat k r) (q : MvPolynomial (Vr (2 * r + k + 1)) ℂ) :
    HasDerivAt (fun t => eval (vars (crv (false, X) g t)) q) (eval (vars g) (dP X q)) 0 := by
  have h := hasDerivAt_eval (fun t => vars (crv (false, X) g t)) (fun i => eval (vars g) (lin X i))
    (fun i => crv_var X g i) q
  have h0 : crv (false, X) g 0 = g := by simp [crv]
  rw [h0] at h
  convert h using 1
  simp only [dP, map_sum, map_mul]
end PI.UnitaryGroupMassFormula.UsCompose

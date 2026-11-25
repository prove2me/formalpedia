-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.hasDerivAt_sv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:14:38.548238+00:00
-- url     : https://prove2.me/submissions/d9ad510f-3274-4be6-9fc8-c22e872aaf8e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_HasDerivAtInvpow
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_hasDerivAt_poly
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_eval_qD
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_eval_qDb
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_hasDerivAt_invpow

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
theorem _root_.solution {k j ρ : ℕ} (X g : Mat k (j + ρ)) (hg : DjU k j ρ g ≠ 0) (s : SC (2 * (j + ρ) + k + 1)) :
    HasDerivAt (fun t => sv k j ρ s (crv (false, X) g t))
      (sv k j ρ (dP X s.1, s.2.1, s.2.2) g
        + sv k j ρ (C (-(s.2.1 : ℂ)) * s.1 * dP X (qD k j ρ), s.2.1 + 1, s.2.2) g
        + sv k j ρ (C (-(s.2.2 : ℂ)) * s.1 * dP X (qDb k j ρ), s.2.1, s.2.2 + 1) g) 0 := by
  obtain ⟨q, a, b⟩ := s
  have hq := hasDerivAt_poly X g q
  have hD : HasDerivAt (fun t => DjU k j ρ (crv (false, X) g t))
      (eval (vars g) (dP X (qD k j ρ))) 0 := by
    simpa only [eval_qD] using hasDerivAt_poly X g (qD k j ρ)
  have hDb : HasDerivAt (fun t => star (DjU k j ρ (crv (false, X) g t)))
      (eval (vars g) (dP X (qDb k j ρ))) 0 := by
    simpa only [eval_qDb] using hasDerivAt_poly X g (qDb k j ρ)
  have h0 : crv (false, X) g 0 = g := by simp [crv]
  have hD0 : DjU k j ρ (crv (false, X) g 0) ≠ 0 := by rw [h0]; exact hg
  have hDb0 : star (DjU k j ρ (crv (false, X) g 0)) ≠ 0 := by rw [h0]; exact star_ne_zero.2 hg
  have h := (hq.mul (hasDerivAt_invpow hD hD0 a)).mul (hasDerivAt_invpow hDb hDb0 b)
  simp only [h0] at h
  refine h.congr_deriv ?_
  simp only [sv, map_mul, eval_C, Pi.mul_apply, h0]
  ring
end PI.UnitaryGroupMassFormula.UsCompose

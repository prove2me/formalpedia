-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure.pd_det_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:07:50.722055+00:00
-- url     : https://prove2.me/submissions/09cacaa4-70a7-47d0-98f8-18d0c385998c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_GfPolyA
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_PolynomialDegreeClosure_pd_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
variable {N : ℕ}
namespace PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure
theorem _root_.solution (n : ℕ) (M : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ i j, IsPolyDeg 1 (fun g => star (M g i j))) : IsPolyDeg n (fun g => star (M g).det) := by
  have e : (fun g => star (M g).det) = fun g => ((M g).map (starRingEnd ℂ)).det := by
    funext g
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, starRingEnd_apply]
  rw [e]
  exact pd_det n _ fun i j => h i j
end PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure

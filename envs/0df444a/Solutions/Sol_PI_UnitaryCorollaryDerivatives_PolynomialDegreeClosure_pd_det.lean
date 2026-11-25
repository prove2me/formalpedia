-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure.pd_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:58:36.685278+00:00
-- url     : https://prove2.me/submissions/889ce812-6c6b-4104-8755-f9b7110effcf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_GfPolyA
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_PolynomialDegreeClosure_pd_cmul
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_PolynomialDegreeClosure_pd_sum
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_PolynomialDegreeClosure_pd_prod

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
    (h : ∀ i j, IsPolyDeg 1 (fun g => M g i j)) : IsPolyDeg n (fun g => (M g).det) := by
  simp only [Matrix.det_apply']
  refine pd_sum _ _ fun σ _ => pd_cmul _ ?_
  have h2 := pd_prod (Finset.univ : Finset (Fin n)) (fun _ => 1) (fun i g => M g (σ i) i)
    (fun i _ => h (σ i) i)
  simpa using h2
end PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure

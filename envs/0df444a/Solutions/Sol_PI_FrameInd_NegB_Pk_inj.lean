-- Prove2me | solution 1 for PI.FrameInd.NegB.Pk_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:40:31.811256+00:00
-- url     : https://prove2.me/submissions/f69ea93a-139e-4a74-aefa-31049bccd210

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_EqZeroOfNegMap
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_sq
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_PJP


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic
noncomputable section
open PI PI.FrameInd PI.FrameInd.NegB
namespace PI.FrameInd.NegB
theorem _root_.solution (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) (h : Pk k r *ᵥ x = 0) : x = 0 := by
  have hA : (Hpk k r * ((Pk k r)ᴴ * Formalism.REAL.Jm (epsK k r))) * Pk k r = 1 := by
    rw [Matrix.mul_assoc, PJP, Hpk_sq]
  calc x = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) *ᵥ x := (Matrix.one_mulVec x).symm
    _ = (Hpk k r * ((Pk k r)ᴴ * Formalism.REAL.Jm (epsK k r))) *ᵥ (Pk k r *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, hA]
    _ = 0 := by rw [h, Matrix.mulVec_zero]
end PI.FrameInd.NegB

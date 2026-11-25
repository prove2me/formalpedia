-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DLm.Lifts.FLW.unitary_of_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:00:31.706521+00:00
-- url     : https://prove2.me/submissions/c574a192-7af6-4815-b8c2-f9c8cadeebc7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFramesCut
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittExtensionTheorem
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFlWitt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped Matrix
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DLm PI.UnitaryGroupMassFormula.DLm.Lifts
open PI.UnitaryGroupMassFormula.DLm.Lifts.FLW
variable {n : ℕ}
namespace PI.UnitaryGroupMassFormula.DLm.Lifts.FLW
theorem _root_.solution (H M : Matrix (Fin n) (Fin n) ℂ) (h : ∀ u v, herm H (M *ᵥ u) (M *ᵥ v) = herm H u v) :
    Mᴴ * H * M = H := by
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  simp only [herm, Matrix.mulVec_single_one] at this
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  convert this using 1
  · simp [dotProduct, Matrix.mulVec, Matrix.col, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
    rw [Finset.sum_comm]
  · simp [dotProduct, Matrix.mulVec, Pi.single_apply]
end PI.UnitaryGroupMassFormula.DLm.Lifts.FLW

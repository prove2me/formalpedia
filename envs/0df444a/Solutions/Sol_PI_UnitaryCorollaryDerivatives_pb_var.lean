-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.pb_var
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:29:35.178106+00:00
-- url     : https://prove2.me/submissions/cc176b91-a262-40f2-896d-9c9baafcbbcd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBB
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_clm

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
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution (i : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    PG 1 (fun g : B.Mat k r => pbVar g i) := by
  rcases i with ⟨a, b⟩ | ⟨a, b⟩
  · have e : (fun g : B.Mat k r => pbVar g (Sum.inl (a, b))) = fun g => pbCo a b g := by
      funext g
      simp [pbVar, pbCo] <;> rfl
    rw [e]
    refine pb_clm (pbCo a b) (fun g => ?_)
    have e2 : pbCo a b g = g a b := by simp [pbCo] <;> rfl
    rw [e2, one_mul]
    exact Matrix.norm_entry_le_entrywise_sup_norm g
  · have e : (fun g : B.Mat k r => pbVar g (Sum.inr (a, b))) = fun g => pbCc a b g := by
      funext g
      simp [pbVar, pbCc] <;> rfl
    rw [e]
    refine pb_clm (pbCc a b) (fun g => ?_)
    have e2 : pbCc a b g = star (g a b) := by simp [pbCc] <;> rfl
    rw [e2, one_mul, norm_star]
    exact Matrix.norm_entry_le_entrywise_sup_norm g
end PI.UnitaryCorollaryDerivatives

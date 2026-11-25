-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.DjC.hpk_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:53:14.847246+00:00
-- url     : https://prove2.me/submissions/73ea8744-b594-4845-aa39-29310dc9b8b6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.DjC
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
variable (k j ρ : ℕ)
namespace PI.UnitaryCorollaryDerivatives.DjC
theorem _root_.solution {k r : ℕ} (i m : Fin (2 * r + k + 1)) (hi : i.val < r) :
    Hpk k r i m = if i.val + m.val = 2 * r + k then 1 else 0 := by
  unfold Hpk
  by_cases h : i.val + m.val = 2 * r + k
  · simp [hi, h]
  · rw [if_neg (fun h' => h h'.2), if_neg (fun h' => h h'.2), if_neg (fun h' => absurd h'.1 (by omega)),
      if_neg h]
end PI.UnitaryCorollaryDerivatives.DjC

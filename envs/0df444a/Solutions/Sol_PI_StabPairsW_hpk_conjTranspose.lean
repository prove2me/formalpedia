-- Prove2me | solution 1 for PI.StabPairsW.hpk_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:09:51.753748+00:00
-- url     : https://prove2.me/submissions/31a703fd-314e-49ed-9cd6-56ed7edfa6b0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Theorems.Thm_PI_StabPairsW_hpk_apply
import Theorems.Thm_PI_StabPairsW_sgI_sgI
import Theorems.Thm_PI_StabPairsW_sgI_eq_iff

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
open PI PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.StabPairsW
theorem _root_.solution : (Hpk k r)ᴴ = Hpk k r := by
  ext i l
  rw [Matrix.conjTranspose_apply, hpk_apply, hpk_apply]
  by_cases h : i.val = sgI k r l.val
  · have h' : l.val = sgI k r i.val := by rw [h, sgI_sgI]
    have hs : (i.val = r + k ↔ l.val = r + k) := by rw [h, sgI_eq_iff]
    rw [if_pos h, if_pos h']
    by_cases hl : l.val = r + k
    · simp [hl, hs.2 hl]
    · have hi : ¬ i.val = r + k := fun h2 => hl (hs.1 h2)
      simp [hl, hi]
  · have h' : ¬ l.val = sgI k r i.val := fun h' => h (by rw [h', sgI_sgI])
    rw [if_neg h, if_neg h']
    simp
end PI.StabPairsW

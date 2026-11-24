-- Prove2me | solution 1 for PI.StabPairsW.herm_es
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:15:41.731599+00:00
-- url     : https://prove2.me/submissions/0b21062f-1426-4dbe-b391-c3d29a3bceba

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Theorems.Thm_PI_StabPairsW_hpk_mulVec
import Theorems.Thm_PI_StabPairsW_herm_bvec

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
theorem _root_.solution (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (esI k r a)) = v (eI k r a) := by
  have ha := a.isLt
  rw [herm_bvec, hpk_mulVec]
  have h1 : ¬ (esI k r a).val = r + k := by simp [esI]; omega
  rw [if_neg h1, one_mul]
  have h2 : sgI k r (2 * r + k - a.val) = a.val := by
    unfold sgI
    rw [if_pos (Or.inr (by omega))]
    omega
  congr 1
  ext
  simp [esI, eI, h2]
end PI.StabPairsW

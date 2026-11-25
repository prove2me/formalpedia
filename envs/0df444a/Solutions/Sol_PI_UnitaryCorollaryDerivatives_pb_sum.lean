-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.pb_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:04:50.442943+00:00
-- url     : https://prove2.me/submissions/de287e9f-cf52-408e-b9f6-e7fb80bcb11b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBB
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_add
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_zero


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
theorem _root_.solution {ι : Type*} (s : Finset ι) {e : ℝ} (F : ι → B.Mat k r → ℂ)
    (hF : ∀ i ∈ s, PG e (F i)) : PG e (fun g => ∑ i ∈ s, F i g) := by
  classical
  revert hF
  refine Finset.induction_on s ?_ ?_
  · intro _
    have h : PG e (fun _ : B.Mat k r => (0 : ℂ)) := pb_zero e
    simpa using h
  · intro a s ha ih hF
    have h1 := hF a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
    convert pb_add h1 h2 using 1
    funext g
    rw [Finset.sum_insert ha]
end PI.UnitaryCorollaryDerivatives

-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.pb_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:09:44.891296+00:00
-- url     : https://prove2.me/submissions/3fb140f0-bd7e-4c9d-8fd5-6452e0c219bd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBB
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_const
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_mul


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
theorem _root_.solution {ι : Type*} (s : Finset ι) (e : ι → ℝ) (F : ι → B.Mat k r → ℂ)
    (hF : ∀ i ∈ s, PG (e i) (F i)) : PG (∑ i ∈ s, e i) (fun g => ∏ i ∈ s, F i g) := by
  classical
  revert hF
  refine Finset.induction_on s ?_ ?_
  · intro _
    have h : PG 0 (fun _ : B.Mat k r => (1 : ℂ)) := pb_const 1
    simpa using h
  · intro a s ha ih hF
    have h1 := hF a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
    rw [Finset.sum_insert ha]
    convert pb_mul h1 h2 using 1
    funext g
    rw [Finset.prod_insert ha]
end PI.UnitaryCorollaryDerivatives

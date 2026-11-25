-- Prove2me | solution 1 for PI.WSF.evA_hw_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:35:55.025298+00:00
-- url     : https://prove2.me/submissions/3210987d-af29-47d9-ae2e-b1df53626e8f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwinLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_ConstructionA
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WSF
open Formalism.BasicNotions MvPolynomial MeasureTheory
namespace PI.WSF
theorem _root_.solution {N : ℕ} (ν : Fin N → ℕ) : evalM 1 (Formalism.GradedWeylDivisibility.hw ℂ (le_refl N) ν) = 1 := by
  have key : ∀ (k : ℕ) (h1 : k ≤ N) (h2 : k ≤ N),
      MvPolynomial.eval (fun v : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) ℂ) v.1 v.2)
        (Formalism.GradedWeylDivisibility.lpMinor ℂ k h1 h2) = 1 := by
    intro k h1 h2
    unfold Formalism.GradedWeylDivisibility.lpMinor
    rw [RingHom.map_det]
    have hM : (MvPolynomial.eval fun v : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) ℂ) v.1 v.2).mapMatrix
        (Matrix.of fun p q : Fin k =>
          (X (Fin.castLE h1 p, Fin.castLE h2 q) : MvPolynomial (Fin N × Fin N) ℂ)) = 1 := by
      ext p q
      simp [Matrix.one_apply]
    rw [hM, Matrix.det_one]
  unfold evalM Formalism.GradedWeylDivisibility.hw
  rw [map_prod]
  exact Finset.prod_eq_one fun s _ => by rw [map_pow, key, one_pow]
end PI.WSF

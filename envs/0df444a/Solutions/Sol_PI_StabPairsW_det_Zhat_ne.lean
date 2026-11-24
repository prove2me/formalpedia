-- Prove2me | solution 1 for PI.StabPairsW.det_Zhat_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:31:23.210736+00:00
-- url     : https://prove2.me/submissions/a0bccc17-cef5-42af-aa9f-86eb9e299f17

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV

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
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) (hS : Std k r z z') (γ : B.Mat k r) (hP : PosPt k r z z' γ) :
    (Zhat k r z z' γ).det ≠ 0 := by
  intro h0
  obtain ⟨_, ⟨_, hT⟩, ⟨_, hT'⟩⟩ := hS
  obtain ⟨_, hG⟩ := hP
  have hD : Dmin k r z z' γ (Fin.last (r + 1)) = 0 := by
    unfold Dmin
    have h1 : (Zhat k r z z' γ).submatrix (Fin.castLE (Nat.le_of_lt_succ (Fin.last (r + 1)).isLt))
        (Fin.castLE (Nat.le_of_lt_succ (Fin.last (r + 1)).isLt)) = Zhat k r z z' γ := by
      ext i j
      rfl
    rw [h1]
    exact h0
  unfold Gf at hG
  rw [hD, Complex.normSq_zero, zero_sub] at hG
  have h2 : 0 ≤ Tz k r z * Tz k r z' * Complex.normSq (Dmin k r z z' γ ⟨r, by omega⟩) :=
    mul_nonneg (mul_nonneg hT.le hT'.le) (Complex.normSq_nonneg _)
  linarith
end PI.StabPairsW

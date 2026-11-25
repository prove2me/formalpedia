-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.pb_entry_le_gN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:35:06.830541+00:00
-- url     : https://prove2.me/submissions/cf481ab6-ea82-4173-8f10-9f8e45dc80d5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBB

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
theorem _root_.solution (M : B.Mat k r) (i j : Fin (2 * r + k + 1)) : ‖M i j‖ ≤ B.gN M := by
  unfold B.gN
  have h1 : ‖M i j‖ ^ 2 ≤ ∑ a, ∑ b, Complex.normSq (M a b) := by
    rw [← Complex.normSq_eq_norm_sq]
    calc Complex.normSq (M i j) ≤ ∑ b, Complex.normSq (M i b) :=
          Finset.single_le_sum (f := fun b => Complex.normSq (M i b))
            (fun b _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ a, ∑ b, Complex.normSq (M a b) :=
          Finset.single_le_sum (f := fun a => ∑ b, Complex.normSq (M a b))
            (fun a _ => Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  calc ‖M i j‖ = Real.sqrt (‖M i j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt h1
end PI.UnitaryCorollaryDerivatives

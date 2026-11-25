-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DLm.av_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:45:01.396977+00:00
-- url     : https://prove2.me/submissions/1360208e-e7e6-472e-a889-cbcefd56fbff

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_DensLemmaOfCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PDownTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DLm
attribute [instance] TopModel.ng TopModel.ns TopModel.cs
namespace PI.UnitaryGroupMassFormula.DLm
theorem _root_.solution (CV r n : ℕ) (hn : 3 ≤ n) : AV (CV / 2) r (n + 1) ≤ AV CV r n := by
  unfold AV
  have h2 : ((CV / 2 : ℕ) : ℝ) * 2 ≤ (CV : ℝ) := by
    have : CV / 2 * 2 ≤ CV := Nat.div_mul_le_self CV 2
    exact_mod_cast this
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hc : (0 : ℝ) ≤ ((CV / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
  have hX : (r : ℝ) ^ 3 * ((n + 1 : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ) ^ 2 + (r : ℝ) ^ 4 ≤
      2 * ((r : ℝ) ^ 3 * n + (n : ℝ) ^ 2 + (r : ℝ) ^ 4) := by
    push_cast
    have hr3 : (0 : ℝ) ≤ (r : ℝ) ^ 3 := by positivity
    have hr4 : (0 : ℝ) ≤ (r : ℝ) ^ 4 := by positivity
    nlinarith
  have hY : (0 : ℝ) ≤ (r : ℝ) ^ 3 * n + (n : ℝ) ^ 2 + (r : ℝ) ^ 4 := by positivity
  calc ((CV / 2 : ℕ) : ℝ) * ((r : ℝ) ^ 3 * ((n + 1 : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ) ^ 2 + (r : ℝ) ^ 4)
      ≤ ((CV / 2 : ℕ) : ℝ) * (2 * ((r : ℝ) ^ 3 * n + (n : ℝ) ^ 2 + (r : ℝ) ^ 4)) :=
        mul_le_mul_of_nonneg_left hX hc
    _ = (((CV / 2 : ℕ) : ℝ) * 2) * ((r : ℝ) ^ 3 * n + (n : ℝ) ^ 2 + (r : ℝ) ^ 4) := by ring
    _ ≤ (CV : ℝ) * ((r : ℝ) ^ 3 * n + (n : ℝ) ^ 2 + (r : ℝ) ^ 4) := mul_le_mul_of_nonneg_right h2 hY
end PI.UnitaryGroupMassFormula.DLm

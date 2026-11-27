-- Prove2me | solution 1 for PI.DatumBlockEigen.Unit.II_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:20:03.894994+00:00
-- url     : https://prove2.me/submissions/00f5f324-9c11-4179-bee4-160c2e33b711

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_IsIntInvOfUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.DatumBlockEigen PI.DatumBlockEigen.Unit
variable {F : Type} [Field F] (O : Subring F) (ϖ : F)
variable {O ϖ}
namespace PI.DatumBlockEigen.Unit
theorem _root_.solution {p q r : ℕ} {y : Matrix (Fin p) (Fin q) F} (hy : y ∈ Formalism.DoubleCosetMeasures.IIset O ϖ)
    {g : Matrix (Fin q) (Fin r) F} (hg : ∀ i j, g i j ∈ O) : y * g ∈ Formalism.DoubleCosetMeasures.IIset O ϖ := by
  intro i j
  choose o ho he using hy
  refine ⟨∑ k, o i k * g k j, O.sum_mem fun k _ => O.mul_mem (ho i k) (hg k j), ?_⟩
  simp only [Matrix.mul_apply, he, Finset.mul_sum, mul_assoc]
end PI.DatumBlockEigen.Unit

-- Prove2me | solution 1 for P2M_PI_DatumConjInvWork_II_mul__0a00f185cfa1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:47:45.336356+00:00
-- url     : https://prove2.me/submissions/35a3107d-44b8-4843-8588-210d42427583

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DatumConjInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugationInvariance_SecondRowsBlockDiagMul

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
open PI PI.DatumConjInvWork
variable {F : Type} [Field F] {a t : ℕ}
namespace PI.DatumConjInvWork
theorem _root_.solution (O : Subring F) (ϖ : F) (y : Matrix (Fin t) (Fin a) F)
    (hy : y ∈ Formalism.DoubleCosetMeasures.IIset O ϖ) (g : Matrix (Fin a) (Fin a) F) (hg : ∀ i j, g i j ∈ O) :
    y * g ∈ Formalism.DoubleCosetMeasures.IIset O ϖ := by
  simp only [Formalism.DoubleCosetMeasures.IIset, Set.mem_setOf_eq] at hy ⊢
  intro i j
  choose o ho hyo using hy
  refine ⟨∑ k, o i k * g k j, Subring.sum_mem O fun k _ => O.mul_mem (ho i k) (hg k j), ?_⟩
  simp only [Matrix.mul_apply, hyo, Finset.mul_sum, mul_assoc]
end PI.DatumConjInvWork

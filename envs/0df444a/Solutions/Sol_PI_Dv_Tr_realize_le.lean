-- Prove2me | solution 1 for PI.Dv.Tr.realize_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:12.465134+00:00
-- url     : https://prove2.me/submissions/dadcbd3c-09d1-4b17-9030-86d180aaafa1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_NormAtAddLe
import Theorems.Thm_Formalism_HN_PlaceOperatorNorms_norm_sq_realize


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv Module NumberField
variable {K : Type} [Field K] [NumberField K] [StarRing K] {V ι : Type} [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
namespace PI.Dv.Tr
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (f : V → V) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ v x, Formalism.HermitianLatticesTheory.normAt b X v (f x) ≤ C * Formalism.HermitianLatticesTheory.normAt b X v x) (x : V) :
    ‖Formalism.HermitianLatticesTheory.realize b X (f x)‖ ≤ C * ‖Formalism.HermitianLatticesTheory.realize b X x‖ := by
  have hsq : ‖Formalism.HermitianLatticesTheory.realize b X (f x)‖ ^ 2 ≤ (C * ‖Formalism.HermitianLatticesTheory.realize b X x‖) ^ 2 := by
    rw [mul_pow, Formalism.HN.PlaceOperatorNorms.norm_sq_realize, Formalism.HN.PlaceOperatorNorms.norm_sq_realize,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (h v x) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
end PI.Dv.Tr

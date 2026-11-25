-- Prove2me | solution 1 for PI.SlopeSteps.expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:22:21.170227+00:00
-- url     : https://prove2.me/submissions/99d3d518-6cda-4f0e-b0bc-5424389e5673

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_GramMatrixDuality
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open PI PI.SlopeSteps
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.L2.DIV
namespace PI.SlopeSteps
theorem _root_.solution {N r : ℕ} {M : Submodule ℤ (MvPolynomial (Fin N × Fin N) ℤ)} (e : Module.Basis (Fin r) ℤ M)
    (p : MvPolynomial (Fin N × Fin N) ℤ) (hp : p ∈ M) :
    intQ N N p = ∑ k, ((e.repr ⟨p, hp⟩ k : ℤ) : ℚ) • intQ N N (e k : MvPolynomial (Fin N × Fin N) ℤ) := by
  have h := congrArg (fun x : M => intQ N N (x : MvPolynomial (Fin N × Fin N) ℤ)) (e.sum_repr ⟨p, hp⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_zsmul] at h
  rw [← h]
  simp only [Int.cast_smul_eq_zsmul]
end PI.SlopeSteps

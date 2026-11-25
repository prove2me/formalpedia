-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.BoxB.hs_unitary_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:40:58.631162+00:00
-- url     : https://prove2.me/submissions/8312c20f-a61c-4437-b61e-7c8f7d0e254e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBoundAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SymmetricDistance_SymDistOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeMultiplicity_EncardLeOfFinset
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBound
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
open Matrix
namespace PI.UnitaryGroupMassFormula.LCG
namespace BoxB
variable {n : ℕ}
section Frob
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing
  Matrix.frobeniusNormedAlgebra Matrix.frobeniusNormedSpace
end Frob
private lemma hs_eq_re_trace_conjTranspose_mul' {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs M = (Mᴴ * M).trace.re := by
  unfold Formalism.REAL.hs
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring
end BoxB
end PI.UnitaryGroupMassFormula.LCG
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.UnitaryGroupMassFormula.LCG.BoxB
variable {n : ℕ}
namespace PI.UnitaryGroupMassFormula.LCG.BoxB
theorem _root_.solution {k : Matrix (Fin n) (Fin n) ℂ} (hk : kᴴ * k = 1) (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs (k * M) = Formalism.REAL.hs M := by
  rw [hs_eq_re_trace_conjTranspose_mul', hs_eq_re_trace_conjTranspose_mul', Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc kᴴ k M, hk,
    Matrix.one_mul]
end PI.UnitaryGroupMassFormula.LCG.BoxB

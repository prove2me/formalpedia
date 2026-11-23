-- Prove2me | solution 1 for PI.WHw.eval_rowGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:38.470646+00:00
-- url     : https://prove2.me/submissions/73460945-d7e2-4226-bad8-63b5dcb4a1f8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ClosedEqNablaC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ConstructionA
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


section
noncomputable section
namespace PI.WHw
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
private theorem eval_rowGen_X_eq_rowAct_one_add_single {N n : ℕ} (a b : Fin N) (t : ℂ) (i : Fin N) (j : Fin n) :
    (rowGen ℂ a b (X (i, j) : MvPolynomial (Fin N × Fin n) ℂ)).eval (C t) =
      rowAct ℂ (1 + Matrix.single b a t) (X (i, j) : MvPolynomial (Fin N × Fin n) ℂ) := by
  have hterm : ∀ c : Fin N, C ((1 + Matrix.single b a t) i c) * (X (c, j) : MvPolynomial (Fin N × Fin n) ℂ) =
      (if c = i then X (i, j) else 0) + (if c = a then (if i = b then C t * X (a, j) else 0) else 0) := by
    intro c
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, ite_and]
    split_ifs <;> subst_vars <;> simp_all [add_mul]
  simp only [rowGen, rowAct, MvPolynomial.aeval_X, hterm, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  by_cases h : i = b
  · simp [h]
    ring
  · simp [h]
end PI.WHw
end
end

set_option autoImplicit false
noncomputable section
open PI PI.WHw
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WHw
theorem _root_.solution {N n : ℕ} (a b : Fin N) (t : ℂ) (f : MvPolynomial (Fin N × Fin n) ℂ) :
    (rowGen ℂ a b f).eval (C t) = rowAct ℂ (1 + Matrix.single b a t) f := by
  induction f using MvPolynomial.induction_on
  · rename_i c
    simp [rowGen, rowAct]
  · rename_i p q hp hq
    simp only [map_add, Polynomial.eval_add, hp, hq]
  · rename_i p v hp
    obtain ⟨i, j⟩ := v
    simp only [map_mul, Polynomial.eval_mul, hp, eval_rowGen_X_eq_rowAct_one_add_single]
end PI.WHw

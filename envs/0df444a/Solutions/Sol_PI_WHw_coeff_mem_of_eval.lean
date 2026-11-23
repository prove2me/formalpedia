-- Prove2me | solution 1 for PI.WHw.coeff_mem_of_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:22.186294+00:00
-- url     : https://prove2.me/submissions/921daf02-cdcf-4c05-8177-07eb22e12143

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



set_option autoImplicit false
noncomputable section
open PI PI.WHw
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WHw
theorem _root_.solution {σ : Type*} (U : Submodule ℂ (MvPolynomial σ ℂ))
    (p : Polynomial (MvPolynomial σ ℂ))
    (h : ∀ n : ℕ, p.eval (C (n : ℂ)) ∈ U) (k : ℕ) : p.coeff k ∈ U := by
  classical
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  obtain ⟨q, hq⟩ : ∃ q : Polynomial ℂ, q = ∑ i ∈ Finset.range (p.natDegree + 1),
      Polynomial.C ((φ.comp U.mkQ) (p.coeff i)) * Polynomial.X ^ i := ⟨_, rfl⟩
  have hroot : ∀ n : ℕ, q.eval (n : ℂ) = 0 := by
    intro n
    have h1 : (φ.comp U.mkQ) (p.eval (C (n : ℂ))) = 0 := by
      rw [LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero U).mpr (h n), map_zero]
    rw [Polynomial.eval_eq_sum_range, map_sum] at h1
    rw [hq, Polynomial.eval_finset_sum, ← h1]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, ← MvPolynomial.C_pow,
      mul_comm (p.coeff i), ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul, mul_comm]
  by_cases hk : k ≤ p.natDegree
  · have hq0 : q = 0 := Polynomial.eq_zero_of_infinite_isRoot q
      (Set.infinite_of_injective_forall_mem Nat.cast_injective (fun n => hroot n))
    have hc := congrArg (fun r => Polynomial.coeff r k) hq0
    simp only [hq, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero,
      Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff.mpr hk, if_true] at hc
    simpa using hc
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp
end PI.WHw

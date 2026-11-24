-- Prove2me | solution 1 for ReciprocityTheory.AnForm.hasFDerivAt_mvPolynomial_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:01.6818+00:00
-- url     : https://prove2.me/submissions/798b8419-efd8-4863-abdd-465450fdfbc4

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_ExistsAnalyticGraphChartMvPolynomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open Function
namespace ReciprocityTheory.AnForm
theorem _root_.solution {n : ℕ} (Q : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    HasFDerivAt (fun y => MvPolynomial.eval y Q)
      (∑ j, MvPolynomial.eval x (MvPolynomial.pderiv j Q) •
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j) x := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval_C, MvPolynomial.pderiv_C, map_zero, zero_smul, Finset.sum_const_zero]
    exact hasFDerivAt_const a x
  | add p q hp hq =>
    simp only [map_add, add_smul, Finset.sum_add_distrib]
    exact hp.add hq
  | mul_X p i hp =>
    have hXi : HasFDerivAt (fun y : Fin n → ℂ => y i)
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i) x := hasFDerivAt_apply i x
    have h2 := hp.mul hXi
    have hfun : (fun y : Fin n → ℂ => MvPolynomial.eval y (p * MvPolynomial.X i)) =
        (fun y => MvPolynomial.eval y p) * (fun y => y i) := by
      funext y
      simp
    have hder : (∑ j, MvPolynomial.eval x (MvPolynomial.pderiv j (p * MvPolynomial.X i)) •
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j) =
        MvPolynomial.eval x p • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i +
          x i • ∑ j, MvPolynomial.eval x (MvPolynomial.pderiv j p) •
            ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j := by
      refine ContinuousLinearMap.ext fun v => ?_
      simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
        Pi.smul_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.add_apply, smul_eq_mul,
        Derivation.leibniz, MvPolynomial.pderiv_X, map_add, MvPolynomial.smul_eval, MvPolynomial.eval_X,
        Pi.single_apply]
      simp only [add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
      simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X]
      have hs : ∑ j, MvPolynomial.eval x (if i = j then p else 0) * v j = MvPolynomial.eval x p * v i := by
        simp [apply_ite, ite_mul, Finset.sum_ite_eq]
      rw [hs]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hfun, hder]
    exact h2
end ReciprocityTheory.AnForm

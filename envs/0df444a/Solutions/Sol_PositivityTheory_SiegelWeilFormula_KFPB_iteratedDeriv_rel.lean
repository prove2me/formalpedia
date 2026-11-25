-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.iteratedDeriv_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:02:44.290329+00:00
-- url     : https://prove2.me/submissions/7dc561b6-cdeb-44a2-baaf-125de6320bae

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IteratedDerivScale
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_iteratedDeriv_scale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Nat
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFPB
namespace PositivityTheory.SiegelWeilFormula.KFPB
theorem _root_.solution (q : Polynomial ℂ) (μ ω : ℂ) (E : ℂ → ℂ) (hE : Differentiable ℂ E) (j : ℕ) :
    iteratedDeriv j (fun z => ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * μ ^ i * E (ω ^ i * z)) 0 =
      q.eval (μ * ω ^ j) * iteratedDeriv j E 0 := by
  have hcomp : ∀ i : ℕ, Differentiable ℂ (fun z => E (ω ^ i * z)) := fun i => by fun_prop
  have hterm : ∀ i ∈ Finset.range (q.natDegree + 1),
      ContDiffAt ℂ (j : WithTop ℕ∞) (fun z => q.coeff i * μ ^ i * E (ω ^ i * z)) 0 := fun i _ =>
    ((hcomp i).const_mul (q.coeff i * μ ^ i)).contDiff.contDiffAt
  rw [iteratedDeriv_fun_sum hterm, Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedDeriv_const_mul _ (hcomp i).contDiff.contDiffAt,
    PositivityTheory.SiegelWeilFormula.KFPB.iteratedDeriv_scale E hE, mul_pow, ← pow_mul, ← pow_mul, mul_comm i j]
  ring
end PositivityTheory.SiegelWeilFormula.KFPB

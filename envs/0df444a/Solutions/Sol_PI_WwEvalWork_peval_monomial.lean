-- Prove2me | solution 1 for PI.WwEvalWork.peval_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:14:43.648318+00:00
-- url     : https://prove2.me/submissions/81d2518f-2bfa-4a33-b40b-0466f461a536

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwEval
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionEvaluation_LsumEqOfSubset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WwEvalWork
open MvPolynomial
variable {σ1 σ2 K : Type*} [CommRing K]
namespace PI.WwEvalWork
theorem _root_.solution (x : σ1 → K) (μ : σ1 ⊕ σ2 →₀ ℕ) (c : ℤ) :
    peval x (monomial μ c) = monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).2
      ((c : K) * (Finsupp.sumFinsuppEquivProdFinsupp μ).1.prod fun v e => x v ^ e) := by
  conv_lhs => rw [← Finsupp.comapDomain_sumElim_comapDomain μ]
  rw [peval, coe_eval₂Hom, eval₂_monomial, Finsupp.prod_sumElim]
  simp only [Finsupp.sumFinsuppEquivProdFinsupp_apply, Function.comp_def, Sum.elim_inl,
    Sum.elim_inr]
  have h1 : ((Finsupp.comapDomain Sum.inl μ Sum.inl_injective.injOn).prod fun v e =>
      (C (x v) : MvPolynomial σ2 K) ^ e) =
      C ((Finsupp.comapDomain Sum.inl μ Sum.inl_injective.injOn).prod fun v e => x v ^ e) := by
    simp [Finsupp.prod, map_prod, map_pow]
  rw [h1, monomial_eq, C_mul, RingHom.comp_apply, eq_intCast, ← mul_assoc]
end PI.WwEvalWork

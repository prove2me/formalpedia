-- Prove2me | solution 1 for PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.chi_psi_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:00:16.663529+00:00
-- url     : https://prove2.me/submissions/38440e4c-9427-4a9a-a4cc-99260d024fa6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_IsWeightedHomogeneousPairingLeft

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.OpWords PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
namespace PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
theorem _root_.solution (i0 : Fin k) (f : Pol K k) :
    tt K k ∣ aeval (chiF K i0) f - aeval (psiF K i0) f := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
  have key : (Ideal.Quotient.mkₐ K (Ideal.span {tt K k})).comp (aeval (chiF K i0)) =
      (Ideal.Quotient.mkₐ K (Ideal.span {tt K k})).comp (aeval (psiF K i0)) := by
    ext v
    simp only [AlgHom.comp_apply, aeval_X, Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    rcases v with j | j
    · simp [chiF, psiF]
    · by_cases hj : j = i0
      · subst hj
        simp only [chiF, psiF, Sum.elim_inr, if_true, eq_self_iff_true]
        have e : X (Sum.inl j) * X (Sum.inr j) - -tp K j = tt K k := by
          rw [sub_neg_eq_add, tp, tt, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
        rw [e]
      · simp [chiF, psiF, hj]
  exact AlgHom.congr_fun key f
end PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords

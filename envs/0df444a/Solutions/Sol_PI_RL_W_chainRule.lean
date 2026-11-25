-- Prove2me | solution 1 for PI.RL.W.chainRule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:18:48.153657+00:00
-- url     : https://prove2.me/submissions/82bcaa83-936f-489c-bfac-8fd4941d6598

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RowLetter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowDerivationChainRule_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowDerivationChainRule_ChainRule
import Theorems.Thm_PI_RL_W_RE_add
import Theorems.Thm_PI_RL_W_RE_C
import Theorems.Thm_PI_RL_W_RE_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial
noncomputable section
namespace PI.RL.W
open PI.RL
section
variable {K : Type} [Field K] {k : ℕ}
private theorem pderiv_mul_eq {σ : Type*} {R : Type*} [CommRing R] (i : σ) (f g : MvPolynomial σ R) :
    pderiv i (f * g) = pderiv i f * g + f * pderiv i g := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
end
private theorem pderiv_X_eq_ite {σ : Type*} {R : Type*} [CommRing R] [DecidableEq σ] (c i : σ) :
    pderiv c (X i : MvPolynomial σ R) = if c = i then 1 else 0 := by
  rw [pderiv_X]
  by_cases h : c = i
  · subst h; simp
  · rw [if_neg h, Pi.single_apply, if_neg (Ne.symm h)]
private theorem derivation_aeval_eq_sum_pderiv {K : Type*} [CommRing K] {σ τ : Type*} [Fintype σ] [DecidableEq σ]
    (D : MvPolynomial τ K → MvPolynomial τ K)
    (hadd : ∀ f g, D (f + g) = D f + D g) (hC : ∀ r, D (C r) = 0)
    (hmul : ∀ f g, D (f * g) = D f * g + f * D g)
    (g : σ → MvPolynomial τ K) (P : MvPolynomial σ K) :
    D (aeval g P) = ∑ c, aeval g (pderiv c P) * D (g c) := by
  induction P using MvPolynomial.induction_on
  next r =>
    rw [aeval_C, MvPolynomial.algebraMap_eq, hC]
    simp
  next p q hp hq =>
    rw [map_add, hadd, hp, hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [map_add, map_add, add_mul]
  next p i ih =>
    have e : ∀ c, aeval g (pderiv c (p * X i)) * D (g c) =
        g i * (aeval g (pderiv c p) * D (g c)) + (if c = i then aeval g p * D (g i) else 0) := by
      intro c
      rw [pderiv_mul_eq, pderiv_X_eq_ite, map_add, map_mul, map_mul, aeval_X]
      by_cases h : c = i
      · subst h; rw [if_pos rfl, if_pos rfl, map_one]; ring
      · rw [if_neg h, if_neg h, map_zero]; ring
    rw [Finset.sum_congr rfl (fun c _ => e c), Finset.sum_add_distrib, ← Finset.mul_sum, ← ih,
      map_mul, aeval_X, hmul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
end PI.RL.W
end
end

set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.RL PI.RL.W
open PI.RL
namespace PI.RL.W
theorem _root_.solution : ChainRule := by
  intro K _ m vec a b P
  simp only [PI.RL.theta]
  exact derivation_aeval_eq_sum_pderiv (PI.RL.RE K (m + 1) a b) (RE_add a b) (RE_C a b)
    (RE_mul a b) _ P
end PI.RL.W

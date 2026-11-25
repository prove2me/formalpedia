-- Prove2me | solution 1 for PI.OpWords.expFormula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:13:53.4032+00:00
-- url     : https://prove2.me/submissions/cc4b25c0-6126-4718-a309-8b5880dab044

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_VanishExp
import Theorems.Thm_PI_OpWords_rop_C
import Theorems.Thm_PI_OpWords_rop_iter_mul_X

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
open PI PI.OpWords
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
namespace PI.OpWords
theorem _root_.solution (a b : Fin k) (hab : a ≠ b) (s : K) (g : Pol K k) : ExpFormula a b s g := by
  unfold ExpFormula
  induction g using MvPolynomial.induction_on
  next r =>
    have hz : ∀ n, (Rop K k a b)^[n + 1] (C r) = 0 := by
      intro n
      rw [Function.iterate_succ_apply, rop_C]
      exact Function.iterate_fixed (map_zero _) n
    refine ⟨0, fun n hn => ?_, fun M _ x => ?_⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact hz m
    · rw [Finset.sum_eq_single 0]
      · simp
      · intro n _ hn
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [hz m]
        simp
      · intro h
        simp at h
  next p q hp hq =>
    obtain ⟨N1, hz1, hs1⟩ := hp
    obtain ⟨N2, hz2, hs2⟩ := hq
    refine ⟨max N1 N2, fun n hn => ?_, fun M hM x => ?_⟩
    · rw [← Module.End.coe_pow, map_add, Module.End.coe_pow, hz1 n (by omega), hz2 n (by omega), add_zero]
    · rw [map_add, hs1 M (by omega) x, hs2 M (by omega) x, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← Module.End.coe_pow, map_add, map_add]
      ring
  next p i hp =>
    obtain ⟨N, hz, hsum⟩ := hp
    refine ⟨N + 1, fun n hn => ?_, fun M hM x => ?_⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [rop_iter_mul_X a b hab p i m, hz (m + 1) (by omega), hz m (by omega)]
      simp
    · have hterm : ∀ m : ℕ, eval x ((Rop K k a b)^[m + 1] (p * X i)) =
          eval x ((Rop K k a b)^[m + 1] p) * x i +
            ((m : K) + 1) * (eval x ((Rop K k a b)^[m] p) * eval x (Rop K k a b (X i))) := by
        intro m
        rw [rop_iter_mul_X a b hab p i m, map_add, eval_mul, eval_X, map_nsmul, eval_mul, nsmul_eq_mul]
        push_cast
        ring
      have hTM : s ^ M / (M.factorial : K) * eval x ((Rop K k a b)^[M] p) = 0 := by
        rw [hz M (by omega), map_zero, mul_zero]
      have hfac : ∀ m : ℕ, s ^ (m + 1) / ((m + 1).factorial : K) * ((m : K) + 1) =
          s * (s ^ m / (m.factorial : K)) := by
        intro m
        have h1 : ((m : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
        have h2 : (m.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
        rw [Nat.factorial_succ, Nat.cast_mul]
        push_cast
        (try field_simp)
        (try ring)
      have hR : ∑ n ∈ Finset.range (M + 1), s ^ n / (n.factorial : K) * eval x ((Rop K k a b)^[n] (p * X i)) =
          ∑ m ∈ Finset.range M, (s ^ (m + 1) / ((m + 1).factorial : K) * eval x ((Rop K k a b)^[m + 1] p) * x i +
            s * eval x (Rop K k a b (X i)) * (s ^ m / (m.factorial : K) * eval x ((Rop K k a b)^[m] p))) +
          s ^ 0 / ((0 : ℕ).factorial : K) * eval x ((Rop K k a b)^[0] p) * x i := by
        rw [Finset.sum_range_succ']
        congr 1
        · refine Finset.sum_congr rfl fun m _ => ?_
          simp only [hterm]
          linear_combination (eval x ((Rop K k a b)^[m] p) * eval x (Rop K k a b (X i))) * hfac m
        · simp
      have hS1 : ∑ n ∈ Finset.range (M + 1), s ^ n / (n.factorial : K) * eval x ((Rop K k a b)^[n] p) =
          ∑ m ∈ Finset.range M, s ^ (m + 1) / ((m + 1).factorial : K) * eval x ((Rop K k a b)^[m + 1] p) +
          s ^ 0 / ((0 : ℕ).factorial : K) * eval x ((Rop K k a b)^[0] p) := Finset.sum_range_succ' _ _
      have hS2 : ∑ n ∈ Finset.range (M + 1), s ^ n / (n.factorial : K) * eval x ((Rop K k a b)^[n] p) =
          ∑ m ∈ Finset.range M, s ^ m / (m.factorial : K) * eval x ((Rop K k a b)^[m] p) := by
        rw [Finset.sum_range_succ, hTM, add_zero]
      have hxi : shiftPt a b s x i = x i + s * eval x (Rop K k a b (X i)) := rfl
      rw [hR, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← hS2, eval_mul, eval_X,
        hsum M (by omega) x, hxi, hS1]
      ring
end PI.OpWords

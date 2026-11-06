-- Prove2me | solution 1 for cancel_main
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:35:48.564176+00:00
-- url     : https://prove2.me/submissions/3a134245-6588-470f-ac41-ea4027b9fa82

import Definitions.Def_PrimeNumberTheoremAnd_Wiener

set_option autoImplicit true
open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate

private theorem cumsum_succ_aux [AddCommMonoid E] {u : ℕ → E} (n : ℕ) :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.sum_range_succ]

private theorem cancel_aux {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤ g (n - 1) * (C * n) + (C * (↑(n - 1 - 1) + 1) * g 0
      - C * (↑(n - 1 - 1) + 1) * g (n - 1) -
    ((n - 1 - 1) • (C * g 0) - ∑ x ∈ Finset.range (n - 1 - 1), C * g (x + 1))) := by
  have l1 (n : ℕ) :
      (g n - g (n + 1)) * ∑ i ∈ Finset.range (n + 1), f i ≤ (g n - g (n + 1)) * (C * (n + 1)) := by
    apply mul_le_mul le_rfl (by simpa only [cumsum, Nat.cast_add, Nat.cast_one] using hf' (n + 1))
      (Finset.sum_nonneg (fun i _ => hf i)) ?_
    simp only [sub_nonneg] ; apply hg' ; simp
  have l2 (x : ℕ) : C * (↑(x + 1) + 1) - C * (↑x + 1) = C := by simp ; ring
  have l3 (n : ℕ) : 0 ≤ cumsum f n := Finset.sum_nonneg (fun i _ => hf i)
  convert_to ∑ i ∈ Finset.range n, (g i) • (f i) ≤ _
  · simp [mul_comm]
  rw [Finset.sum_range_by_parts, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  simp_rw [← neg_smul, neg_sub, smul_eq_mul]
  apply _root_.add_le_add
  · exact mul_le_mul le_rfl (hf' n) (l3 n) (hg _)
  · refine (Finset.sum_le_sum (fun n _ => l1 n)).trans ?_
    calc
      (∑ i ∈ Finset.range (n - 1), (g i - g (i + 1)) * (C * (↑i + 1))) =
          ∑ i ∈ Finset.range (n - 1), (C * (↑i + 1)) • (g i - g (i + 1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [mul_comm]
      _ ≤ _ := by
        rw [Finset.sum_range_by_parts]
        simp_rw [Finset.sum_range_sub', l2, smul_sub, smul_eq_mul, Finset.sum_sub_distrib,
          Finset.sum_const, Finset.card_range]
        apply le_of_eq
        ring_nf

private theorem sum_range_succ_aux (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, a (i + 1) = (∑ i ∈ Finset.range (n + 1), a i) - a 0 := by
  have := Finset.sum_range_sub a n
  rw [Finset.sum_sub_distrib, sub_eq_iff_eq_add] at this
  rw [Finset.sum_range_succ, this] ; ring

private theorem cancel_aux' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤
        C * n * g (n - 1)
      + C * cumsum g (n - 1 - 1 + 1)
      - C * (↑(n - 1 - 1) + 1) * g (n - 1) := by
  have := cancel_aux hf hg hf' hg' n
  simp only [nsmul_eq_mul, ← Finset.mul_sum, sum_range_succ_aux] at this
  convert this using 1 ; unfold cumsum ; ring

theorem solution {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) (hn : 2 ≤ n) :
    cumsum (f * g) n ≤ C * cumsum g n := by
  change (∑ i ∈ Finset.range n, f i * g i) ≤ C * cumsum g n
  refine (cancel_aux' hf hg hf' hg' n).trans_eq ?_
  have hindex : n - 1 - 1 + 1 = n - 1 := by omega
  have hcast : (n : ℝ) = ↑(n - 1) + 1 := by
    exact_mod_cast (show n = (n - 1) + 1 by omega)
  have hcast' : (↑(n - 1 - 1) : ℝ) + 1 = ↑(n - 1) := by
    exact_mod_cast hindex
  have hsum : cumsum g n = cumsum g (n - 1) + g (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    exact cumsum_succ_aux (n - 1)
  rw [hindex, hcast', hcast, hsum]
  ring

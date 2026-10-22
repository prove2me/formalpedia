-- Prove2me | solution 1 for PosteriorSamplingRL.Regret.appB_sqrt_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:34:37.321317+00:00
-- url     : https://prove2.me/submissions/9b6248ac-16b2-4b9b-a8c5-5321cddbff80

import Mathlib
import Definitions.Def_PosteriorSamplingRL_Regret_Confidence
set_option autoImplicit false
open PosteriorSamplingRL.Regret

lemma psr2_visit_eq_sum {S A τ : ℕ} (sa : ℕ → Fin τ → Fin S × Fin A) (k : ℕ) (p : Fin S × Fin A) :
    visitCount sa k p = ∑ l ∈ Finset.range k, (Finset.univ.filter (fun j : Fin τ => sa l j = p)).card := by
  unfold visitCount
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.card_filter]

lemma psr2_regroup {S A τ : ℕ} (sa : ℕ → Fin τ → Fin S × Fin A) (m : ℕ)
    (F : ℕ → Fin S × Fin A → ℝ) :
    ∑ k ∈ Finset.range m, ∑ j : Fin τ, F k (sa k j) =
      ∑ p : Fin S × Fin A, ∑ k ∈ Finset.range m,
        ((Finset.univ.filter (fun j : Fin τ => sa k j = p)).card : ℝ) * F k p := by
  classical
  have h1 : ∀ k j, F k (sa k j) = ∑ p : Fin S × Fin A, if sa k j = p then F k p else 0 := by
    intro k j
    rw [Finset.sum_ite_eq]; simp
  simp_rw [h1]
  rw [Finset.sum_congr rfl (fun k _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

lemma psr2_term (τ N n : ℕ) (hn : n ≤ τ) :
    (n : ℝ) * (if τ < N then 1 / Real.sqrt N else 0) ≤
      2 * Real.sqrt 2 * (Real.sqrt ((N : ℝ) + n) - Real.sqrt N) := by
  have hmono : Real.sqrt N ≤ Real.sqrt ((N : ℝ) + n) :=
    Real.sqrt_le_sqrt (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  by_cases h : τ < N
  · simp only [h, if_true]
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    set a := Real.sqrt N with ha
    set b := Real.sqrt ((N : ℝ) + n) with hb
    have hapos : 0 < a := Real.sqrt_pos.2 hNpos
    have ha2 : a ^ 2 = N := Real.sq_sqrt hNpos.le
    have hb2 : b ^ 2 = (N : ℝ) + n := Real.sq_sqrt (by positivity)
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (show n ≤ N by omega)
    have hble : b ≤ Real.sqrt 2 * a := by
      rw [hb, ha, ← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt (by linarith)
    have hn_eq : (n : ℝ) = (b - a) * (b + a) := by nlinarith
    rw [mul_one_div, div_le_iff₀ hapos]
    rw [hn_eq]
    have : (b - a) * (b + a) ≤ (b - a) * (2 * Real.sqrt 2 * a) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      nlinarith
    nlinarith
  · simp only [h, if_false, mul_zero]
    have : 0 ≤ 2 * Real.sqrt 2 := by positivity
    exact mul_nonneg this (by linarith)

lemma psr2_seq (τ : ℕ) (n : ℕ → ℕ) (hn : ∀ k, n k ≤ τ) (m : ℕ) :
    ∑ k ∈ Finset.range m, (n k : ℝ) *
        (if τ < ∑ l ∈ Finset.range k, n l then 1 / Real.sqrt ((∑ l ∈ Finset.range k, n l : ℕ) : ℝ) else 0) ≤
      2 * Real.sqrt 2 * Real.sqrt ((∑ l ∈ Finset.range m, n l : ℕ) : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have h := psr2_term τ (∑ l ∈ Finset.range m, n l) (n m) (hn m)
    have e : (((∑ l ∈ Finset.range (m + 1), n l : ℕ)) : ℝ) =
        ((∑ l ∈ Finset.range m, n l : ℕ) : ℝ) + (n m : ℝ) := by
      rw [Finset.sum_range_succ]; push_cast; ring
    rw [e]
    linarith

theorem solution (S A τ : ℕ) (sa : ℕ → Fin τ → Fin S × Fin A) (m : ℕ) :
    ∑ k ∈ Finset.range m, ∑ j : Fin τ,
        (if τ < visitCount sa k (sa k j) then 1 / Real.sqrt (visitCount sa k (sa k j)) else 0)
      ≤ Real.sqrt (8 * (S : ℝ) * A * ((m : ℝ) * τ)) := by
  classical
  set nn : Fin S × Fin A → ℕ → ℕ := fun p k => (Finset.univ.filter (fun j : Fin τ => sa k j = p)).card with hnn
  have hnn_le : ∀ p k, nn p k ≤ τ := by
    intro p k
    calc nn p k ≤ (Finset.univ : Finset (Fin τ)).card := Finset.card_filter_le _ _
      _ = τ := by simp
  have hvis : ∀ k p, visitCount sa k p = ∑ l ∈ Finset.range k, nn p l :=
    fun k p => psr2_visit_eq_sum sa k p
  rw [psr2_regroup sa m (fun k p => if τ < visitCount sa k p then 1 / Real.sqrt (visitCount sa k p) else 0)]
  have hper : ∀ p : Fin S × Fin A, ∑ k ∈ Finset.range m, (nn p k : ℝ) *
      (if τ < visitCount sa k p then 1 / Real.sqrt (visitCount sa k p) else 0) ≤
        2 * Real.sqrt 2 * Real.sqrt (visitCount sa m p) := by
    intro p
    have := psr2_seq τ (nn p) (hnn_le p) m
    simpa [hvis] using this
  have hsum : ∑ p : Fin S × Fin A, (visitCount sa m p : ℝ) = (m : ℝ) * τ := by
    have h1 : ∑ p : Fin S × Fin A, visitCount sa m p = m * τ := by
      have := Finset.card_eq_sum_card_fiberwise (f := fun lj : ℕ × Fin τ => sa lj.1 lj.2)
        (s := Finset.range m ×ˢ (Finset.univ : Finset (Fin τ))) (t := Finset.univ)
        (fun _ _ => Finset.mem_univ _)
      rw [Finset.card_product] at this
      simpa [visitCount] using this.symm
    exact_mod_cast h1
  calc _ ≤ ∑ p : Fin S × Fin A, 2 * Real.sqrt 2 * Real.sqrt (visitCount sa m p) := Finset.sum_le_sum (fun p _ => hper p)
    _ = 2 * Real.sqrt 2 * ∑ p : Fin S × Fin A, Real.sqrt (visitCount sa m p) := by rw [Finset.mul_sum]
    _ ≤ Real.sqrt (8 * (S : ℝ) * A * ((m : ℝ) * τ)) := by
      have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin S × Fin A)))
        (f := fun p => Real.sqrt (visitCount sa m p))
      have hsq : ∑ p : Fin S × Fin A, Real.sqrt (visitCount sa m p) ^ 2 = (m : ℝ) * τ := by
        rw [← hsum]
        exact Finset.sum_congr rfl (fun p _ => Real.sq_sqrt (Nat.cast_nonneg _))
      rw [hsq] at hcs
      simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hcs
      apply Real.le_sqrt_of_sq_le
      have h8 : (2 * Real.sqrt 2) ^ 2 = 8 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
      calc (2 * Real.sqrt 2 * ∑ p : Fin S × Fin A, Real.sqrt (visitCount sa m p)) ^ 2
          = 8 * (∑ p : Fin S × Fin A, Real.sqrt (visitCount sa m p)) ^ 2 := by rw [mul_pow, h8]
        _ ≤ 8 * (((S * A : ℕ) : ℝ) * ((m : ℝ) * τ)) := by gcongr
        _ = 8 * (S : ℝ) * A * ((m : ℝ) * τ) := by push_cast; ring

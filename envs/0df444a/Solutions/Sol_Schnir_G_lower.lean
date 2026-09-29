-- Prove2me | solution 1 for Schnir.G_lower
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T22:55:18.422974+00:00
-- url     : https://prove2.me/submissions/e1e33931-b7f1-4b99-81d7-460b05ff351c

import Mathlib
import Definitions.Def_Schnir_defs

open Finset Real

namespace Schnir

/-- Integers in `[1, M]` all of whose prime factors lie in `P`. -/
def gbound_DA (P : Finset ℕ) (M : ℕ) : Finset ℕ :=
  (Icc 1 M).filter (fun n => n.primeFactors ⊆ P)

/-- Squarefree integers in `[1, M]` all of whose prime factors lie in `P`. -/
def gbound_DS (P : Finset ℕ) (M : ℕ) : Finset ℕ :=
  (Icc 1 M).filter (fun n => Squarefree n ∧ n.primeFactors ⊆ P)

/-- `x(d) = ∏_{p ∣ d} 1/(p-1)` (equals `1/φ(d)` on squarefree `d`). -/
noncomputable def gbound_x (d : ℕ) : ℝ := ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 1)

lemma gbound_pf_mul {q m : ℕ} (hq : q.Prime) (hm : m ≠ 0) :
    (q * m).primeFactors = insert q m.primeFactors := by
  rw [Nat.primeFactors_mul hq.ne_zero hm, hq.primeFactors, Finset.insert_eq]

lemma gbound_x_mul {q m : ℕ} (hq : q.Prime) (hm : m ≠ 0) (hqm : ¬ q ∣ m) :
    gbound_x (q * m) = 1 / ((q : ℝ) - 1) * gbound_x m := by
  unfold gbound_x
  rw [gbound_pf_mul hq hm, Finset.prod_insert]
  intro h; exact hqm (Nat.dvd_of_mem_primeFactors h)

lemma gbound_h_mul (s : ℕ) {q m : ℕ} (hq : q.Prime) (hm : m ≠ 0) (hqm : ¬ q ∣ m) :
    hfun s (q * m) = ((rho s q : ℝ) / ((q : ℝ) - (rho s q : ℝ))) * hfun s m := by
  unfold hfun
  rw [gbound_pf_mul hq hm, Finset.prod_insert]
  intro h; exact hqm (Nat.dvd_of_mem_primeFactors h)

lemma gbound_x_nonneg (d : ℕ) : 0 ≤ gbound_x d := by
  unfold gbound_x
  apply Finset.prod_nonneg
  intro p hp
  have := (Nat.prime_of_mem_primeFactors hp).two_le
  have : (2:ℝ) ≤ p := by exact_mod_cast this
  apply div_nonneg <;> linarith

lemma gbound_h_nonneg (s d : ℕ) : 0 ≤ hfun s d := by
  unfold hfun
  apply Finset.prod_nonneg
  intro p hp
  have := (Nat.prime_of_mem_primeFactors hp).two_le
  have : (2:ℝ) ≤ p := by exact_mod_cast this
  unfold rho
  split_ifs <;> push_cast <;> apply div_nonneg <;> linarith

lemma gbound_sum_DA_insert (P : Finset ℕ) {q : ℕ} (hq : q.Prime) (hqP : q ∉ P) (M : ℕ)
    (w : ℕ → ℝ) :
    ∑ n ∈ gbound_DA (insert q P) M, w n =
      ∑ n ∈ gbound_DA P M, w n + ∑ n ∈ gbound_DA (insert q P) (M / q), w (q * n) := by
  rw [← Finset.sum_filter_not_add_sum_filter _ (fun n => q ∣ n)]
  congr 1
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext n
    simp only [gbound_DA, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun p hp => ?_⟩
      rcases Finset.mem_insert.1 (h2 hp) with h | h
      · subst h; exact absurd (Nat.dvd_of_mem_primeFactors hp) h3
      · exact h
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, h2.trans (Finset.subset_insert _ _)⟩, fun h => hqP ?_⟩
      exact h2 (Nat.mem_primeFactors.2 ⟨hq, h, by omega⟩)
  · apply Finset.sum_nbij' (fun n => n / q) (fun n => q * n)
    · intro n hn
      simp only [gbound_DA, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hn
      have hqn : q ≤ n := Nat.le_of_dvd (by omega) h4
      refine ⟨⟨Nat.div_pos hqn hq.pos, Nat.div_le_div_right h2⟩, ?_⟩
      exact (Nat.primeFactors_mono (Nat.div_dvd_of_dvd h4) (by omega)).trans h3
    · intro n hn
      simp only [gbound_DA, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      obtain ⟨⟨h1, h2⟩, h3⟩ := hn
      refine ⟨⟨⟨Nat.mul_pos hq.pos h1, ?_⟩, ?_⟩, dvd_mul_right _ _⟩
      · have := (Nat.le_div_iff_mul_le hq.pos).1 h2; linarith
      · rw [gbound_pf_mul hq (by omega)]
        exact Finset.insert_subset (Finset.mem_insert_self _ _) h3
    · intro n hn
      simp only [gbound_DA, Finset.mem_filter] at hn
      exact Nat.mul_div_cancel' hn.2
    · intro n _
      exact Nat.mul_div_cancel_left n hq.pos
    · intro n hn
      simp only [gbound_DA, Finset.mem_filter] at hn
      rw [Nat.mul_div_cancel' hn.2]

lemma gbound_sum_DS_insert (P : Finset ℕ) {q : ℕ} (hq : q.Prime) (hqP : q ∉ P) (M : ℕ)
    (w : ℕ → ℝ) :
    ∑ n ∈ gbound_DS (insert q P) M, w n =
      ∑ n ∈ gbound_DS P M, w n + ∑ n ∈ gbound_DS P (M / q), w (q * n) := by
  rw [← Finset.sum_filter_not_add_sum_filter _ (fun n => q ∣ n)]
  congr 1
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext n
    simp only [gbound_DS, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h0, h2⟩, h3⟩
      refine ⟨h1, h0, fun p hp => ?_⟩
      rcases Finset.mem_insert.1 (h2 hp) with h | h
      · subst h; exact absurd (Nat.dvd_of_mem_primeFactors hp) h3
      · exact h
    · rintro ⟨h1, h0, h2⟩
      refine ⟨⟨h1, h0, h2.trans (Finset.subset_insert _ _)⟩, fun h => hqP ?_⟩
      exact h2 (Nat.mem_primeFactors.2 ⟨hq, h, by omega⟩)
  · apply Finset.sum_nbij' (fun n => n / q) (fun n => q * n)
    · intro n hn
      simp only [gbound_DS, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      obtain ⟨⟨⟨h1, h2⟩, h0, h3⟩, h4⟩ := hn
      have hqn : q ≤ n := Nat.le_of_dvd (by omega) h4
      obtain ⟨m, rfl⟩ := h4
      have hm0 : m ≠ 0 := by rintro rfl; simp at h1
      rw [Nat.mul_div_cancel_left m hq.pos]
      have hsq := (Nat.squarefree_mul_iff.1 h0)
      have hqm : ¬ q ∣ m := fun h => by
        exact hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hsq.1 h)
      refine ⟨⟨Nat.pos_of_ne_zero hm0, (Nat.le_div_iff_mul_le hq.pos).2 (by linarith)⟩, hsq.2.2, ?_⟩
      intro p hp
      have := h3 (by rw [gbound_pf_mul hq hm0]; exact Finset.mem_insert_of_mem hp)
      rcases Finset.mem_insert.1 this with h | h
      · subst h; exact absurd (Nat.dvd_of_mem_primeFactors hp) hqm
      · exact h
    · intro n hn
      simp only [gbound_DS, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      obtain ⟨⟨h1, h2⟩, h0, h3⟩ := hn
      have hqn : ¬ q ∣ n := fun h => hqP (h3 (Nat.mem_primeFactors.2 ⟨hq, h, by omega⟩))
      refine ⟨⟨⟨Nat.mul_pos hq.pos h1, ?_⟩, ?_, ?_⟩, dvd_mul_right _ _⟩
      · have := (Nat.le_div_iff_mul_le hq.pos).1 h2; linarith
      · exact Nat.squarefree_mul_iff.2 ⟨(Nat.Prime.coprime_iff_not_dvd hq).2 hqn,
          hq.prime.squarefree, h0⟩
      · rw [gbound_pf_mul hq (by omega)]
        exact Finset.insert_subset (Finset.mem_insert_self _ _)
          (h3.trans (Finset.subset_insert _ _))
    · intro n hn
      simp only [gbound_DS, Finset.mem_filter] at hn
      exact Nat.mul_div_cancel' hn.2
    · intro n _
      exact Nat.mul_div_cancel_left n hq.pos
    · intro n hn
      simp only [gbound_DS, Finset.mem_filter] at hn
      rw [Nat.mul_div_cancel' hn.2]

noncomputable def gbound_Rx (P : Finset ℕ) (M : ℕ) : ℝ := ∑ d ∈ gbound_DS P M, gbound_x d
noncomputable def gbound_U (P : Finset ℕ) (M : ℕ) : ℝ := ∑ n ∈ gbound_DA P M, (1 : ℝ) / n
noncomputable def gbound_R (s : ℕ) (P : Finset ℕ) (M : ℕ) : ℝ := ∑ d ∈ gbound_DS P M, hfun s d
noncomputable def gbound_L (P : Finset ℕ) (M : ℕ) : ℝ :=
  ∑ a ∈ gbound_DS P M, gbound_x a * gbound_Rx P (M / a)
noncomputable def gbound_CP (s : ℕ) (P : Finset ℕ) : ℝ :=
  ∏ p ∈ P.filter (· ∣ s), (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2)

lemma gbound_DS_mono (P : Finset ℕ) {K M : ℕ} (h : K ≤ M) : gbound_DS P K ⊆ gbound_DS P M := by
  intro n hn
  simp only [gbound_DS, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
  exact ⟨⟨hn.1.1, hn.1.2.trans h⟩, hn.2⟩

lemma gbound_DS_zero (P : Finset ℕ) : gbound_DS P 0 = ∅ := by
  ext n; simp [gbound_DS]

lemma gbound_mem_DS {P : Finset ℕ} {M n : ℕ} (h : n ∈ gbound_DS P M) :
    1 ≤ n ∧ n ≤ M ∧ Squarefree n ∧ n.primeFactors ⊆ P := by
  simp only [gbound_DS, Finset.mem_filter, Finset.mem_Icc] at h
  exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩

lemma gbound_not_dvd_of_mem_DS {P : Finset ℕ} {q M n : ℕ} (hq : q.Prime) (hqP : q ∉ P)
    (h : n ∈ gbound_DS P M) : ¬ q ∣ n := by
  obtain ⟨h1, -, -, h3⟩ := gbound_mem_DS h
  exact fun hd => hqP (h3 (Nat.mem_primeFactors.2 ⟨hq, hd, by omega⟩))

lemma gbound_Rx_insert (P : Finset ℕ) {q : ℕ} (hq : q.Prime) (hqP : q ∉ P) (K : ℕ) :
    gbound_Rx (insert q P) K = gbound_Rx P K + 1 / ((q : ℝ) - 1) * gbound_Rx P (K / q) := by
  unfold gbound_Rx
  rw [gbound_sum_DS_insert P hq hqP, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have := (gbound_mem_DS hn).1
  exact gbound_x_mul hq (by omega) (gbound_not_dvd_of_mem_DS hq hqP hn)

lemma gbound_R_insert (s : ℕ) (P : Finset ℕ) {q : ℕ} (hq : q.Prime) (hqP : q ∉ P) (K : ℕ) :
    gbound_R s (insert q P) K = gbound_R s P K +
      ((rho s q : ℝ) / ((q : ℝ) - (rho s q : ℝ))) * gbound_R s P (K / q) := by
  unfold gbound_R
  rw [gbound_sum_DS_insert P hq hqP, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have := (gbound_mem_DS hn).1
  exact gbound_h_mul s hq (by omega) (gbound_not_dvd_of_mem_DS hq hqP hn)

lemma gbound_U_insert (P : Finset ℕ) {q : ℕ} (hq : q.Prime) (hqP : q ∉ P) (K : ℕ) :
    gbound_U (insert q P) K = gbound_U P K + 1 / (q : ℝ) * gbound_U (insert q P) (K / q) := by
  unfold gbound_U
  rw [gbound_sum_DA_insert P hq hqP, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  push_cast
  rw [one_div_mul_one_div]

lemma gbound_R_nonneg (s : ℕ) (P : Finset ℕ) (K : ℕ) : 0 ≤ gbound_R s P K :=
  Finset.sum_nonneg (fun d _ => gbound_h_nonneg s d)

lemma gbound_Rx_nonneg (P : Finset ℕ) (K : ℕ) : 0 ≤ gbound_Rx P K :=
  Finset.sum_nonneg (fun d _ => gbound_x_nonneg d)

lemma gbound_R_mono (s : ℕ) (P : Finset ℕ) {K M : ℕ} (h : K ≤ M) :
    gbound_R s P K ≤ gbound_R s P M :=
  Finset.sum_le_sum_of_subset_of_nonneg (gbound_DS_mono P h)
    (fun d _ _ => gbound_h_nonneg s d)

lemma gbound_L_restrict (P : Finset ℕ) {K M : ℕ} (h : K ≤ M) :
    ∑ a ∈ gbound_DS P M, gbound_x a * gbound_Rx P (K / a) = gbound_L P K := by
  unfold gbound_L
  symm
  apply Finset.sum_subset (gbound_DS_mono P h)
  intro a ha ha'
  obtain ⟨h1, h2, h3, h4⟩ := gbound_mem_DS ha
  have hKa : K < a := by
    by_contra hc
    apply ha'
    simp only [gbound_DS, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨h1, by omega⟩, h3, h4⟩
  rw [Nat.div_eq_of_lt hKa]
  simp [gbound_Rx, gbound_DS_zero]

lemma gbound_L_insert (P : Finset ℕ) {q : ℕ} (hq : q.Prime) (hqP : q ∉ P) (M : ℕ) :
    gbound_L (insert q P) M = gbound_L P M + 2 * (1 / ((q : ℝ) - 1)) * gbound_L P (M / q) +
      (1 / ((q : ℝ) - 1)) ^ 2 * gbound_L P (M / q / q) := by
  set c := 1 / ((q : ℝ) - 1)
  have e1 : gbound_L (insert q P) M =
      ∑ a ∈ gbound_DS P M, gbound_x a * gbound_Rx (insert q P) (M / a) +
      ∑ a ∈ gbound_DS P (M / q), gbound_x (q * a) * gbound_Rx (insert q P) (M / (q * a)) := by
    unfold gbound_L
    rw [gbound_sum_DS_insert P hq hqP]
  have e2 : ∑ a ∈ gbound_DS P M, gbound_x a * gbound_Rx (insert q P) (M / a) =
      gbound_L P M + c * gbound_L P (M / q) := by
    rw [← gbound_L_restrict P (Nat.div_le_self M q), Finset.mul_sum]
    unfold gbound_L
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [gbound_Rx_insert P hq hqP, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm a q]
    ring
  have e3 : ∑ a ∈ gbound_DS P (M / q), gbound_x (q * a) * gbound_Rx (insert q P) (M / (q * a)) =
      c * gbound_L P (M / q) + c ^ 2 * gbound_L P (M / q / q) := by
    rw [← gbound_L_restrict P (Nat.div_le_self (M / q) q), Finset.mul_sum]
    unfold gbound_L
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    have := (gbound_mem_DS ha).1
    rw [gbound_x_mul hq (by omega) (gbound_not_dvd_of_mem_DS hq hqP ha),
      gbound_Rx_insert P hq hqP, ← Nat.div_div_eq_div_mul]
    have : M / q / a / q = M / q / q / a := by
      simp only [Nat.div_div_eq_div_mul]; congr 1; ring
    rw [this]
    ring
  rw [e1, e2, e3]; ring

lemma gbound_Rx_mono (P : Finset ℕ) {K M : ℕ} (h : K ≤ M) :
    gbound_Rx P K ≤ gbound_Rx P M :=
  Finset.sum_le_sum_of_subset_of_nonneg (gbound_DS_mono P h)
    (fun d _ _ => gbound_x_nonneg d)

lemma gbound_DA_empty (M : ℕ) : gbound_DA ∅ M ⊆ {1} := by
  intro n hn
  simp only [gbound_DA, Finset.mem_filter, Finset.mem_Icc, Finset.subset_empty,
    Nat.primeFactors_eq_empty] at hn
  simp only [Finset.mem_singleton]; omega

lemma gbound_DS_empty (M : ℕ) : gbound_DS ∅ M ⊆ {1} := by
  intro n hn
  simp only [gbound_DS, Finset.mem_filter, Finset.mem_Icc, Finset.subset_empty,
    Nat.primeFactors_eq_empty] at hn
  simp only [Finset.mem_singleton]; omega

lemma gbound_DS_eq_DA_empty (M : ℕ) : gbound_DS ∅ M = gbound_DA ∅ M := by
  ext n
  constructor
  · intro hn
    have := gbound_DS_empty M hn
    simp only [gbound_DS, gbound_DA, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.2⟩
  · intro hn
    have := gbound_DA_empty M hn
    rw [Finset.mem_singleton] at this
    subst this
    simp only [gbound_DS, gbound_DA, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, squarefree_one, hn.2⟩

lemma gbound_step_i (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∀ M, gbound_U P M ≤ gbound_Rx P M := by
  induction P using Finset.induction_on with
  | empty =>
    intro M
    unfold gbound_U gbound_Rx
    rw [gbound_DS_eq_DA_empty]
    apply Finset.sum_le_sum
    intro n hn
    have := gbound_DA_empty M hn
    rw [Finset.mem_singleton] at this
    subst this
    simp [gbound_x]
  | @insert q P hqP ih =>
    have hq : q.Prime := hP q (Finset.mem_insert_self _ _)
    have ih := ih (fun p hp => hP p (Finset.mem_insert_of_mem hp))
    intro M
    induction M using Nat.strong_induction_on with
    | _ M ihM =>
      rcases Nat.eq_zero_or_pos M with h0 | hMpos
      · subst h0
        simp [gbound_U, gbound_Rx, gbound_DA, gbound_DS]
      have h2 := ihM (M / q) (Nat.div_lt_self hMpos hq.one_lt)
      rw [gbound_Rx_insert P hq hqP] at h2
      rw [gbound_U_insert P hq hqP, gbound_Rx_insert P hq hqP]
      have h1 := ih M
      have h3 := gbound_Rx_mono P (Nat.div_le_self (M / q) q)
      have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
      have hc : 0 ≤ 1 / ((q : ℝ) - 1) := by apply div_nonneg <;> linarith
      have hiq : 0 ≤ 1 / (q : ℝ) := by apply div_nonneg <;> linarith
      have key : 1 / (q : ℝ) * (1 + 1 / ((q : ℝ) - 1)) = 1 / ((q : ℝ) - 1) := by
        have : (q : ℝ) - 1 ≠ 0 := by linarith
        have : (q : ℝ) ≠ 0 := by linarith
        field_simp; ring
      calc gbound_U P M + 1 / (q : ℝ) * gbound_U (insert q P) (M / q)
          ≤ gbound_Rx P M + 1 / (q : ℝ) * (gbound_Rx P (M / q) +
              1 / ((q : ℝ) - 1) * gbound_Rx P (M / q / q)) := by
            gcongr
        _ ≤ gbound_Rx P M + 1 / (q : ℝ) * (gbound_Rx P (M / q) +
              1 / ((q : ℝ) - 1) * gbound_Rx P (M / q)) := by gcongr
        _ = gbound_Rx P M + 1 / ((q : ℝ) - 1) * gbound_Rx P (M / q) := by
            linear_combination (gbound_Rx P (M / q)) * key

lemma gbound_CP_nonneg (s : ℕ) (P : Finset ℕ) : 0 ≤ gbound_CP s P := by
  unfold gbound_CP
  apply Finset.prod_nonneg
  intro p _
  positivity

lemma gbound_step_iii (s : ℕ) (hs : Even s) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∀ M, gbound_L P M ≤ gbound_CP s P * gbound_R s P M := by
  induction P using Finset.induction_on with
  | empty =>
    intro M
    have hC : gbound_CP s ∅ = 1 := by simp [gbound_CP]
    rw [hC, one_mul]
    rcases Finset.subset_singleton_iff.1 (gbound_DS_empty M) with h | h
    · simp [gbound_L, gbound_R, h]
    · have h' : ∀ K, gbound_DS ∅ K ⊆ {1} := gbound_DS_empty
      simp only [gbound_L, gbound_R, h, Finset.sum_singleton, Nat.div_one, gbound_Rx]
      simp [gbound_x, hfun]
  | @insert q P hqP ih =>
    have hq : q.Prime := hP q (Finset.mem_insert_self _ _)
    have ih := ih (fun p hp => hP p (Finset.mem_insert_of_mem hp))
    intro M
    rw [gbound_L_insert P hq hqP, gbound_R_insert s P hq hqP]
    have hCP := gbound_CP_nonneg s P
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
    have hc : 0 ≤ 1 / ((q : ℝ) - 1) := by apply div_nonneg <;> linarith
    set c := 1 / ((q : ℝ) - 1) with hc_def
    have hA := gbound_R_nonneg s P M
    have hAB := gbound_R_mono s P (Nat.div_le_self M q)
    have hBD := gbound_R_mono s P (Nat.div_le_self (M / q) q)
    have hD := gbound_R_nonneg s P (M / q / q)
    set A := gbound_R s P M
    set B := gbound_R s P (M / q)
    set D := gbound_R s P (M / q / q)
    have hL : gbound_L P M + 2 * c * gbound_L P (M / q) + c ^ 2 * gbound_L P (M / q / q) ≤
        gbound_CP s P * A + 2 * c * (gbound_CP s P * B) + c ^ 2 * (gbound_CP s P * D) := by
      have := ih M; have := ih (M / q); have := ih (M / q / q)
      gcongr
    have hLB : gbound_L P M + 2 * c * gbound_L P (M / q) + c ^ 2 * gbound_L P (M / q / q) ≤
        gbound_CP s P * (A + (2 * c + c ^ 2) * B) := by
      nlinarith [mul_nonneg (mul_nonneg hCP (sq_nonneg c)) (sub_nonneg.2 hBD)]
    have hCins : gbound_CP s (insert q P) =
        (if q ∣ s then (1 + (q : ℝ) / ((q : ℝ) - 1) ^ 2) else 1) * gbound_CP s P := by
      unfold gbound_CP
      rw [Finset.filter_insert]
      split_ifs with h
      · rw [Finset.prod_insert (fun h' => hqP (Finset.mem_filter.1 h').1)]
      · rw [one_mul]
    rw [hCins]
    by_cases hqs : q ∣ s
    · have hrho : (rho s q : ℝ) = 1 := by simp [rho, hqs]
      rw [if_pos hqs, hrho]
      have hk : (q : ℝ) / ((q : ℝ) - 1) ^ 2 = c + c ^ 2 := by
        have : (q : ℝ) - 1 ≠ 0 := by linarith
        rw [hc_def]; field_simp; ring
      rw [hk]
      have hc1 : (1 : ℝ) / ((q : ℝ) - 1) = c := rfl
      rw [hc1]
      refine hLB.trans ?_
      nlinarith [mul_nonneg (mul_nonneg hCP (add_nonneg hc (sq_nonneg c))) (sub_nonneg.2 hAB),
        mul_nonneg (mul_nonneg (mul_nonneg hCP (add_nonneg hc (sq_nonneg c))) hc)
          (gbound_R_nonneg s P (M / q))]
    · have hrho : (rho s q : ℝ) = 2 := by simp [rho, hqs]
      rw [if_neg hqs, hrho, one_mul]
      have hq3 : (3 : ℝ) ≤ q := by
        have : q ≠ 2 := by rintro rfl; exact hqs (even_iff_two_dvd.1 hs)
        have : 3 ≤ q := by have := hq.two_le; omega
        exact_mod_cast this
      have hh : 2 * c + c ^ 2 ≤ 2 / ((q : ℝ) - 2) := by
        have h1 : (q : ℝ) - 1 ≠ 0 := by linarith
        have e : 2 * c + c ^ 2 = (2 * (q : ℝ) - 1) / (((q : ℝ) - 1) ^ 2) := by
          rw [hc_def]; field_simp; ring
        rw [e, div_le_div_iff₀ (by positivity) (by linarith)]
        nlinarith
      refine hLB.trans ?_
      have hB := gbound_R_nonneg s P (M / q)
      nlinarith [mul_nonneg hCP (mul_nonneg (sub_nonneg.2 hh) hB)]

lemma gbound_log_le_sum_inv (K : ℕ) :
    Real.log ((K : ℝ) + 1) ≤ ∑ b ∈ Icc 1 K, (1 : ℝ) / b := by
  have := log_add_one_le_harmonic K
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at this
  push_cast at this
  simpa [one_div] using this

lemma gbound_tele (N : ℕ) :
    (Real.log ((N : ℝ) + 1)) ^ 2 / 2 ≤
      ∑ a ∈ Icc 1 N, (1 : ℝ) / a * Real.log (((N : ℝ) + 1) / a) := by
  set L := Real.log ((N : ℝ) + 1) with hL
  have claim : ∀ n, n ≤ N → (L ^ 2 - (L - Real.log ((n : ℝ) + 1)) ^ 2) / 2 ≤
      ∑ a ∈ Icc 1 n, (1 : ℝ) / a * (L - Real.log a) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [Finset.sum_Icc_succ_top (by omega)]
      have ih := ih (by omega)
      push_cast
      have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hlog : Real.log ((n : ℝ) + 1 + 1) - Real.log ((n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
        rw [← Real.log_div (by positivity) (by positivity)]
        have := Real.log_le_sub_one_of_pos (x := ((n : ℝ) + 1 + 1) / ((n : ℝ) + 1))
          (by positivity)
        have e : ((n : ℝ) + 1 + 1) / ((n : ℝ) + 1) - 1 = 1 / ((n : ℝ) + 1) := by
          field_simp; ring
        linarith
      have hmono : Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1 + 1) :=
        Real.log_le_log hn0 (by linarith)
      have hv : Real.log ((n : ℝ) + 1 + 1) ≤ L := by
        rw [hL]; apply Real.log_le_log (by positivity)
        have : ((n + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hn
        push_cast at this; linarith
      set u := L - Real.log ((n : ℝ) + 1)
      set v := L - Real.log ((n : ℝ) + 1 + 1)
      have huv : u - v ≤ 1 / ((n : ℝ) + 1) := by simp only [u, v]; linarith
      have huv0 : 0 ≤ u - v := by simp only [u, v]; linarith
      have hv0 : 0 ≤ v := by simp only [v]; linarith
      have hu : 0 ≤ u := by linarith
      have key : u ^ 2 - v ^ 2 ≤ 2 * (1 / ((n : ℝ) + 1) * u) := by
        nlinarith [mul_le_mul_of_nonneg_right huv (by linarith : (0:ℝ) ≤ u + v)]
      linarith
  have h := claim N le_rfl
  rw [← hL] at h
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero] at h
  refine h.trans (le_of_eq (Finset.sum_congr rfl ?_))
  intro a ha
  have : (0 : ℝ) < a := by
    have := (Finset.mem_Icc.1 ha).1; exact_mod_cast this
  rw [Real.log_div (by positivity) this.ne']

lemma gbound_harm_cmp (N : ℕ) :
    ∑ a ∈ Icc 1 N, (1 : ℝ) / a * Real.log (((N : ℝ) + 1) / a) ≤
      ∑ a ∈ Icc 1 N, (1 : ℝ) / a * ∑ b ∈ Icc 1 (N / a), (1 : ℝ) / b := by
  apply Finset.sum_le_sum
  intro a ha
  have ha1 := (Finset.mem_Icc.1 ha).1
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine le_trans ?_ (gbound_log_le_sum_inv (N / a))
  apply Real.log_le_log (by positivity)
  rw [div_le_iff₀ ha0]
  have h := Nat.lt_mul_div_succ N (show 0 < a by omega)
  have h' : ((N + 1 : ℕ) : ℝ) ≤ ((a * (N / a + 1) : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  linarith

lemma gbound_DA_full (P : Finset ℕ) (K : ℕ) (hP : ∀ p, p.Prime → p ≤ K → p ∈ P) :
    gbound_DA P K = Icc 1 K := by
  ext n
  simp only [gbound_DA, Finset.mem_filter, Finset.mem_Icc, and_iff_left_iff_imp]
  intro h p hp
  exact hP p (Nat.prime_of_mem_primeFactors hp)
    ((Nat.le_of_mem_primeFactors hp).trans h.2)

lemma gbound_DS_full (P : Finset ℕ) (K : ℕ) (hP : ∀ p, p.Prime → p ≤ K → p ∈ P) :
    gbound_DS P K = (Icc 1 K).filter Squarefree := by
  ext n
  simp only [gbound_DS, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, h2, fun p hp => ?_⟩
    exact hP p (Nat.prime_of_mem_primeFactors hp)
      ((Nat.le_of_mem_primeFactors hp).trans h1.2)

lemma gbound_swap (P : Finset ℕ) (N : ℕ) :
    ∑ a ∈ gbound_DA P N, (1 : ℝ) / a * gbound_Rx P (N / a) =
      ∑ b ∈ gbound_DS P N, gbound_x b * gbound_U P (N / b) := by
  unfold gbound_Rx gbound_U
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm' (t' := gbound_DS P N) (s' := fun b => gbound_DA P (N / b))]
  · apply Finset.sum_congr rfl; intro b _; apply Finset.sum_congr rfl; intro a _; ring
  · intro a b
    simp only [gbound_DA, gbound_DS, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨ha1, haN⟩, haP⟩, ⟨hb1, hbN⟩, hbs, hbP⟩
      have hab : b * a ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 hbN
      refine ⟨⟨⟨ha1, (Nat.le_div_iff_mul_le (by omega)).2 (by linarith)⟩, haP⟩,
        ⟨hb1, ?_⟩, hbs, hbP⟩
      nlinarith
    · rintro ⟨⟨⟨ha1, haN⟩, haP⟩, ⟨hb1, hbN⟩, hbs, hbP⟩
      have hab : a * b ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 haN
      refine ⟨⟨⟨ha1, ?_⟩, haP⟩, ⟨hb1, (Nat.le_div_iff_mul_le (by omega)).2 (by linarith)⟩,
        hbs, hbP⟩
      nlinarith

/-- Note eq. (10): `G_s(z) ≥ (log z)^2 / (2 C(s))` for positive even `s` and `z > 1`. -/
theorem G_lower (s : ℕ) (hs : Even s) (hs0 : 0 < s) (z : ℝ) (hz : 1 < z) :
    (Real.log z) ^ 2 / (2 * C s) ≤ G s z := by
  set N := ⌊z⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by push_cast; linarith)
  have hzN : z < (N : ℝ) + 1 := Nat.lt_floor_add_one z
  set P := (Finset.range (N + s + 1)).filter Nat.Prime with hPdef
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.1 hp).2
  have hPfull : ∀ K, K ≤ N → ∀ p, p.Prime → p ≤ K → p ∈ P := by
    intro K hK p hp hpK
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hp⟩
  have hG : G s z = gbound_R s P N := by
    unfold G gbound_R
    rw [gbound_DS_full P N (hPfull N le_rfl)]
  have hC : gbound_CP s P = C s := by
    unfold gbound_CP C
    apply Finset.prod_congr _ (fun _ _ => rfl)
    ext p
    simp only [hPdef, Finset.mem_filter, Finset.mem_range, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨_, hp⟩, hd⟩; exact ⟨hp, hd, by omega⟩
    · rintro ⟨hp, hd, -⟩
      have := Nat.le_of_dvd hs0 hd
      exact ⟨⟨by omega, hp⟩, hd⟩
  have hCpos : 0 < C s := by
    unfold C
    apply Finset.prod_pos
    intro p _
    positivity
  -- the analytic lower bound
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have hlog1 : Real.log z ≤ Real.log ((N : ℝ) + 1) := Real.log_le_log (by linarith) hzN.le
  have hsq : (Real.log z) ^ 2 ≤ (Real.log ((N : ℝ) + 1)) ^ 2 :=
    pow_le_pow_left₀ hlogz.le hlog1 2
  have h1 := gbound_tele N
  have h2 := gbound_harm_cmp N
  have h3 : ∑ a ∈ Icc 1 N, (1 : ℝ) / a * ∑ b ∈ Icc 1 (N / a), (1 : ℝ) / b =
      ∑ a ∈ gbound_DA P N, (1 : ℝ) / a * gbound_U P (N / a) := by
    rw [gbound_DA_full P N (hPfull N le_rfl)]
    apply Finset.sum_congr rfl
    intro a _
    unfold gbound_U
    rw [gbound_DA_full P (N / a) (hPfull _ (Nat.div_le_self N a))]
  have h4 : ∑ a ∈ gbound_DA P N, (1 : ℝ) / a * gbound_U P (N / a) ≤
      ∑ a ∈ gbound_DA P N, (1 : ℝ) / a * gbound_Rx P (N / a) := by
    apply Finset.sum_le_sum
    intro a _
    exact mul_le_mul_of_nonneg_left (gbound_step_i P hPp _) (by positivity)
  have h5 := gbound_swap P N
  have h6 : ∑ b ∈ gbound_DS P N, gbound_x b * gbound_U P (N / b) ≤ gbound_L P N := by
    unfold gbound_L
    apply Finset.sum_le_sum
    intro b _
    exact mul_le_mul_of_nonneg_left (gbound_step_i P hPp _) (gbound_x_nonneg b)
  have h7 := gbound_step_iii s hs P hPp N
  rw [hC, ← hG] at h7
  rw [div_le_iff₀ (by positivity)]
  nlinarith

end Schnir

open Schnir in
theorem solution (s : ℕ) (hs : Even s) (hs0 : 0 < s) (z : ℝ) (hz : 1 < z) :
    (Real.log z) ^ 2 / (2 * C s) ≤ G s z :=
  Schnir.G_lower s hs hs0 z hz

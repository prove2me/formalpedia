-- Prove2me | solution 1 for SecretaryAdvice.SamplesDual.t_reduction
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:26:52.801405+00:00
-- url     : https://prove2.me/submissions/91673956-3681-47db-a715-4a08c9dfad05

import Mathlib
import Definitions.Def_SecretaryAdvice_SamplesDual_ClosedForm

set_option autoImplicit false
open Finset
open SecretaryAdvice.SamplesDual

/-- `∏_{ℓ=1}^{j} (a + ℓ)` -/
noncomputable def SADP (a : ℝ) (j : ℕ) : ℝ := ∏ ℓ ∈ Icc 1 j, (a + ℓ)

/-- rising factorial `y (y+1) ... (y+r-1)` -/
noncomputable def SADQ (y : ℝ) (r : ℕ) : ℝ := ∏ u ∈ range r, (y + u)

lemma SADP_zero (a : ℝ) : SADP a 0 = 1 := by simp [SADP]

lemma SADP_succ (a : ℝ) (j : ℕ) : SADP a (j + 1) = SADP a j * (a + ((j : ℝ) + 1)) := by
  unfold SADP
  rw [Finset.prod_Icc_succ_top (by omega)]
  push_cast
  ring

lemma SADQ_zero (y : ℝ) : SADQ y 0 = 1 := by simp [SADQ]

lemma SADQ_succ (y : ℝ) (r : ℕ) : SADQ y (r + 1) = SADQ y r * (y + r) := by
  unfold SADQ
  rw [Finset.prod_range_succ]

lemma SADQ_succ' (y : ℝ) (r : ℕ) : SADQ y (r + 1) = y * SADQ (y + 1) r := by
  unfold SADQ
  have : ∏ k ∈ range r, (y + ((k + 1 : ℕ) : ℝ)) = ∏ u ∈ range r, (y + 1 + (u : ℝ)) :=
    Finset.prod_congr rfl (fun u _ => by push_cast; ring)
  rw [Finset.prod_range_succ', this, Nat.cast_zero, add_zero, mul_comm]

lemma SAD_prodIcc (f : ℕ → ℝ) (i : ℕ) (hi : 1 ≤ i) :
    ∀ r : ℕ, ∏ t ∈ Icc i (i + r - 1), f t = ∏ u ∈ range r, f (i + u) := by
  intro r
  induction r with
  | zero =>
    rw [Finset.Icc_eq_empty (by omega)]
    simp
  | succ r ih =>
    rw [Finset.prod_range_succ, ← ih]
    have : i + (r + 1) - 1 = (i + r - 1) + 1 := by omega
    rw [this, Finset.prod_Icc_succ_top (by omega)]
    congr 2
    omega

lemma SAD_sumIcc1 (N : ℕ) (f : ℕ → ℝ) :
    ∑ j ∈ Icc 1 N, f j = ∑ j ∈ range N, f (j + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]


lemma tred_unfold (n k i : ℕ) (hin : i < n) (s : Fin (k + 1)) :
    samplesUnclipped n k i s = coeffA n k s - ∑ j ∈ Ioc i n, ∑ s' : Fin (k + 1),
      samplesUnclipped n k j s' * coeffC s' i s := by
  unfold samplesUnclipped
  rw [unclippedDual, if_pos hin]
  congr 1
  exact Finset.sum_attach (Finset.Ioc i n) (fun j => ∑ s' : Fin (k + 1),
      unclippedDual n (S := Fin (k + 1)) (fun _ s => coeffA n k s) (fun _ s' i s => coeffC s' i s) j s' *
        coeffC s' i s)



lemma SADQ_add (y : ℝ) (r1 r2 : ℕ) : SADQ y (r1 + r2) = SADQ y r1 * SADQ (y + r1) r2 := by
  unfold SADQ
  rw [Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro u _
  push_cast
  ring

lemma SADQ_pos (y : ℝ) (hy : 0 < y) (r : ℕ) : 0 < SADQ y r := by
  unfold SADQ
  apply Finset.prod_pos
  intro u _
  have : (0 : ℝ) ≤ u := Nat.cast_nonneg u
  linarith

lemma SAD_Icc_to_Q (x : ℝ) (a r b : ℕ) (ha : 1 ≤ a) (hb : b + 1 = a + r) :
    ∏ t ∈ Icc a b, (x + (t : ℝ)) = SADQ (x + a) r := by
  have hb' : b = a + r - 1 := by omega
  rw [hb', SAD_prodIcc (fun t => x + (t : ℝ)) a ha r]
  unfold SADQ
  apply Finset.prod_congr rfl
  intro u _
  push_cast
  ring

lemma SAD_Icc_to_Q' (x : ℝ) (a r b : ℕ) (ha : 1 ≤ a) (hb : b + 1 = a + r) :
    ∏ t ∈ Icc a b, (x + (t : ℝ) + 1) = SADQ (x + a + 1) r := by
  have := SAD_Icc_to_Q (x + 1) a r b ha hb
  rw [← show x + 1 + (a : ℝ) = x + a + 1 by ring] 
  rw [← this]
  apply Finset.prod_congr rfl
  intro t _
  ring

lemma tred_inner (n k i j s s' : ℕ) (hi : 1 ≤ i) (hij : i < j) (hjn : j < n) (hss : s ≤ s') :
    innerFormula n k j s' * coeffC s' i s =
      (∏ t ∈ Icc 1 (i - 1), ((s : ℝ) + t)) / (((k : ℝ) + 1) * ∏ t ∈ Icc 1 (n - 1), ((k : ℝ) + t + 1)) *
        ((∏ t ∈ Icc (i + 1) (n - 1), ((s' : ℝ) + t)) -
          ∑ m ∈ Icc 1 (n - j), ((n - j).choose m : ℝ) * (1 / (m : ℝ)) *
            (∏ ℓ ∈ Icc 1 m, ((k : ℝ) - s' + ℓ)) *
            ∏ t ∈ Icc (i + 1) (n - m - 1), ((s' : ℝ) + t)) := by
  unfold innerFormula
  rw [coeffC, if_pos hss]
  have hs'1 : (0 : ℝ) < (s' : ℝ) + 1 := by positivity
  have hs'2 : (0 : ℝ) < (s' : ℝ) + 2 := by positivity
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hkj : (0 : ℝ) < (k : ℝ) + j + 1 := by positivity
  -- products
  have a1 : ∏ t ∈ Icc 1 (j - 1), ((s' : ℝ) + t) / ((k : ℝ) + t + 1) =
      SADQ ((s' : ℝ) + 1) (j - 1) / SADQ ((k : ℝ) + 2) (j - 1) := by
    rw [Finset.prod_div_distrib, SAD_Icc_to_Q (s' : ℝ) 1 (j - 1) (j - 1) le_rfl (by omega),
      SAD_Icc_to_Q' (k : ℝ) 1 (j - 1) (j - 1) le_rfl (by omega)]
    norm_num
    ring_nf
  have a2 : ∏ t ∈ Icc j (n - 1), ((s' : ℝ) + t) / ((k : ℝ) + t + 1) =
      SADQ ((s' : ℝ) + j) (n - j) / SADQ ((k : ℝ) + j + 1) (n - j) := by
    rw [Finset.prod_div_distrib, SAD_Icc_to_Q (s' : ℝ) j (n - j) (n - 1) (by omega) (by omega),
      SAD_Icc_to_Q' (k : ℝ) j (n - j) (n - 1) (by omega) (by omega)]
  have b2 : ∏ t ∈ Icc j (n - 1), ((k : ℝ) + t + 1) = SADQ ((k : ℝ) + j + 1) (n - j) :=
    SAD_Icc_to_Q' (k : ℝ) j (n - j) (n - 1) (by omega) (by omega)
  have c1 : ∏ t ∈ Icc 1 (i - 1), ((s : ℝ) + t) / ((s' : ℝ) + t + 1) =
      SADQ ((s : ℝ) + 1) (i - 1) / SADQ ((s' : ℝ) + 2) (i - 1) := by
    rw [Finset.prod_div_distrib, SAD_Icc_to_Q (s : ℝ) 1 (i - 1) (i - 1) le_rfl (by omega),
      SAD_Icc_to_Q' (s' : ℝ) 1 (i - 1) (i - 1) le_rfl (by omega)]
    norm_num
    ring_nf
  have pi' : ∏ t ∈ Icc 1 (n - 1), ((k : ℝ) + t + 1) = SADQ ((k : ℝ) + 2) (n - 1) := by
    rw [SAD_Icc_to_Q' (k : ℝ) 1 (n - 1) (n - 1) le_rfl (by omega)]
    norm_num
    ring_nf
  have ps : ∏ t ∈ Icc 1 (i - 1), ((s : ℝ) + t) = SADQ ((s : ℝ) + 1) (i - 1) :=
    by
    have := SAD_Icc_to_Q (s : ℝ) 1 (i - 1) (i - 1) le_rfl (by omega)
    simpa using this
  have xx : ∏ t ∈ Icc (i + 1) (n - 1), ((s' : ℝ) + t) = SADQ ((s' : ℝ) + i + 1) (n - 1 - i) := by
    rw [SAD_Icc_to_Q (s' : ℝ) (i + 1) (n - 1 - i) (n - 1) (by omega) (by omega)]
    push_cast; ring_nf
  have ssq : ∀ m : ℕ, ∏ ℓ ∈ Icc 1 (n - j - m), ((s' : ℝ) + j - 1 + ℓ) =
      SADQ ((s' : ℝ) + j) (n - j - m) := by
    intro m
    have := SAD_Icc_to_Q ((s' : ℝ) + j - 1) 1 (n - j - m) (n - j - m) le_rfl (by omega)
    rw [this]
    congr 1
    push_cast
    ring
  have hcast1 : ((j - 1 - i : ℕ) : ℝ) = (j : ℝ) - 1 - i := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    simp
  have hcast2 : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  set Y := SADQ ((s' : ℝ) + i + 1) (j - 1 - i) with hYdef
  set Z := SADQ ((s' : ℝ) + j) (n - j) with hZdef
  have hY : SADQ ((s' : ℝ) + 1) (j - 1) = SADQ ((s' : ℝ) + 1) i * Y := by
    have := SADQ_add ((s' : ℝ) + 1) i (j - 1 - i)
    rw [show i + (j - 1 - i) = j - 1 by omega] at this
    rw [this, hYdef]
    congr 2
    ring
  have hZ : SADQ ((s' : ℝ) + i + 1) (n - 1 - i) = Y * Z := by
    have := SADQ_add ((s' : ℝ) + i + 1) (j - 1 - i) (n - j)
    rw [show j - 1 - i + (n - j) = n - 1 - i by omega] at this
    rw [this, hcast1]
    congr 2
    ring
  have hP : SADQ ((k : ℝ) + 2) (n - 1) =
      SADQ ((k : ℝ) + 2) (j - 1) * SADQ ((k : ℝ) + j + 1) (n - j) := by
    have := SADQ_add ((k : ℝ) + 2) (j - 1) (n - j)
    rw [show j - 1 + (n - j) = n - 1 by omega] at this
    rw [this, hcast2]
    congr 2
    ring
  have hD : SADQ ((s' : ℝ) + 1) i = ((s' : ℝ) + 1) * SADQ ((s' : ℝ) + 2) (i - 1) := by
    have := SADQ_succ' ((s' : ℝ) + 1) (i - 1)
    rw [show i - 1 + 1 = i by omega] at this
    rw [this]
    congr 2
    ring
  have hprod : ∀ m ∈ Icc 1 (n - j),
      ∏ t ∈ Icc (i + 1) (n - m - 1), ((s' : ℝ) + t) = Y * SADQ ((s' : ℝ) + j) (n - j - m) := by
    intro m hm
    have hm' := Finset.mem_Icc.1 hm
    rw [SAD_Icc_to_Q (s' : ℝ) (i + 1) (n - m - 1 - i) (n - m - 1) (by omega) (by omega)]
    have := SADQ_add ((s' : ℝ) + i + 1) (j - 1 - i) (n - j - m)
    rw [show j - 1 - i + (n - j - m) = n - m - 1 - i by omega] at this
    push_cast at this ⊢
    rw [show (s' : ℝ) + (i + 1 : ℝ) = (s' : ℝ) + i + 1 by ring, this, hcast1]
    congr 2
    ring
  have hsum : ∑ m ∈ Icc 1 (n - j), ((n - j).choose m : ℝ) * (1 / (m : ℝ)) *
        (∏ ℓ ∈ Icc 1 m, ((k : ℝ) - s' + ℓ)) * ∏ t ∈ Icc (i + 1) (n - m - 1), ((s' : ℝ) + t) =
      Y * ∑ m ∈ Icc 1 (n - j), ((n - j).choose m : ℝ) * (1 / (m : ℝ)) *
        (∏ ℓ ∈ Icc 1 m, ((k : ℝ) - s' + ℓ)) * SADQ ((s' : ℝ) + j) (n - j - m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [hprod m hm]
    ring
  rw [a1, a2, b2, c1, pi', ps, xx, hsum]
  simp only [ssq]
  rw [hY, hZ, hP, hD]
  have hYpos : 0 < SADQ ((s' : ℝ) + 2) (i - 1) := SADQ_pos _ hs'2 _
  have hp1 : 0 < SADQ ((k : ℝ) + 2) (j - 1) := SADQ_pos _ hk2 _
  have hB2 : 0 < SADQ ((k : ℝ) + j + 1) (n - j) := SADQ_pos _ hkj _
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  field_simp

lemma tred_top (n k i s s' : ℕ) (hi : 1 ≤ i) (hin : i < n) (hss : s ≤ s') :
    unclippedFormula n k n s' * coeffC s' i s =
      (∏ t ∈ Icc 1 (i - 1), ((s : ℝ) + t)) / (((k : ℝ) + 1) * ∏ t ∈ Icc 1 (n - 1), ((k : ℝ) + t + 1)) *
        (∏ t ∈ Icc (i + 1) (n - 1), ((s' : ℝ) + t)) := by
  unfold unclippedFormula coeffA
  rw [if_pos rfl, coeffC, if_pos hss]
  have hs'1 : (0 : ℝ) < (s' : ℝ) + 1 := by positivity
  have hs'2 : (0 : ℝ) < (s' : ℝ) + 2 := by positivity
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have a1 : ∏ t ∈ Icc 1 (n - 1), ((s' : ℝ) + t) / ((k : ℝ) + t + 1) =
      SADQ ((s' : ℝ) + 1) (n - 1) / SADQ ((k : ℝ) + 2) (n - 1) := by
    rw [Finset.prod_div_distrib, SAD_Icc_to_Q (s' : ℝ) 1 (n - 1) (n - 1) le_rfl (by omega),
      SAD_Icc_to_Q' (k : ℝ) 1 (n - 1) (n - 1) le_rfl (by omega)]
    norm_num
    ring_nf
  have c1 : ∏ t ∈ Icc 1 (i - 1), ((s : ℝ) + t) / ((s' : ℝ) + t + 1) =
      SADQ ((s : ℝ) + 1) (i - 1) / SADQ ((s' : ℝ) + 2) (i - 1) := by
    rw [Finset.prod_div_distrib, SAD_Icc_to_Q (s : ℝ) 1 (i - 1) (i - 1) le_rfl (by omega),
      SAD_Icc_to_Q' (s' : ℝ) 1 (i - 1) (i - 1) le_rfl (by omega)]
    norm_num
    ring_nf
  have pi' : ∏ t ∈ Icc 1 (n - 1), ((k : ℝ) + t + 1) = SADQ ((k : ℝ) + 2) (n - 1) := by
    rw [SAD_Icc_to_Q' (k : ℝ) 1 (n - 1) (n - 1) le_rfl (by omega)]
    norm_num
    ring_nf
  have ps : ∏ t ∈ Icc 1 (i - 1), ((s : ℝ) + t) = SADQ ((s : ℝ) + 1) (i - 1) := by
    have := SAD_Icc_to_Q (s : ℝ) 1 (i - 1) (i - 1) le_rfl (by omega)
    simpa using this
  have xx : ∏ t ∈ Icc (i + 1) (n - 1), ((s' : ℝ) + t) = SADQ ((s' : ℝ) + i + 1) (n - 1 - i) := by
    rw [SAD_Icc_to_Q (s' : ℝ) (i + 1) (n - 1 - i) (n - 1) (by omega) (by omega)]
    push_cast; ring_nf
  have hX : SADQ ((s' : ℝ) + 1) (n - 1) =
      SADQ ((s' : ℝ) + 1) i * SADQ ((s' : ℝ) + i + 1) (n - 1 - i) := by
    have := SADQ_add ((s' : ℝ) + 1) i (n - 1 - i)
    rw [show i + (n - 1 - i) = n - 1 by omega] at this
    rw [this]
    congr 2
    ring
  have hD : SADQ ((s' : ℝ) + 1) i = ((s' : ℝ) + 1) * SADQ ((s' : ℝ) + 2) (i - 1) := by
    have := SADQ_succ' ((s' : ℝ) + 1) (i - 1)
    rw [show i - 1 + 1 = i by omega] at this
    rw [this]
    congr 2
    ring
  rw [a1, c1, pi', ps, xx, hX, hD]
  have hYpos : 0 < SADQ ((s' : ℝ) + 2) (i - 1) := SADQ_pos _ hs'2 _
  have hp1 : 0 < SADQ ((k : ℝ) + 2) (n - 1) := SADQ_pos _ hk2 _
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  field_simp

lemma tred_sumT (n k i s s' : ℕ) (hi : 1 ≤ i) (hin : i < n) (hss : s ≤ s') :
    ∑ j ∈ Ioc i n, unclippedFormula n k j s' * coeffC s' i s =
      (∏ t ∈ Icc 1 (i - 1), ((s : ℝ) + t)) /
        (((k : ℝ) + 1) * ∏ t ∈ Icc 1 (n - 1), ((k : ℝ) + t + 1)) * T n k i s' := by
  set K : ℝ := (∏ t ∈ Icc 1 (i - 1), ((s : ℝ) + t)) /
        (((k : ℝ) + 1) * ∏ t ∈ Icc 1 (n - 1), ((k : ℝ) + t + 1)) with hK
  set X : ℝ := ∏ t ∈ Icc (i + 1) (n - 1), ((s' : ℝ) + t) with hX
  have hI : Ioc i n = insert n (Ioc i (n - 1)) := by
    ext j
    simp only [mem_Ioc, mem_insert]
    omega
  have hnI : n ∉ Ioc i (n - 1) := by
    simp only [mem_Ioc]
    omega
  rw [hI, Finset.sum_insert hnI, tred_top n k i s s' hi hin hss]
  have h1 : ∀ j ∈ Ioc i (n - 1), unclippedFormula n k j s' * coeffC s' i s =
      K * (X - ∑ m ∈ Icc 1 (n - j), ((n - j).choose m : ℝ) * (1 / (m : ℝ)) *
            (∏ ℓ ∈ Icc 1 m, ((k : ℝ) - s' + ℓ)) *
            ∏ t ∈ Icc (i + 1) (n - m - 1), ((s' : ℝ) + t)) := by
    intro j hj
    have hj' := mem_Ioc.1 hj
    unfold unclippedFormula
    rw [if_neg (by omega)]
    exact tred_inner n k i j s s' hi hj'.1 (by omega) hss
  rw [Finset.sum_congr rfl h1]
  have hIcc : Icc (i + 1) (n - 1) = Ioc i (n - 1) := by
    ext j
    simp only [mem_Icc, mem_Ioc]
    omega
  unfold T
  rw [← hX, hIcc]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, ← Finset.mul_sum]
  have hcard : ((n - 1 - i : ℕ) : ℝ) + 1 = (n : ℝ) - i := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  linear_combination (K * X) * hcard

theorem solution (n k i : ℕ) (hi : 1 ≤ i) (hin : i < n)
    (ih : ∀ i' : ℕ, i < i' → i' ≤ n → ∀ s' : Fin (k + 1),
      samplesUnclipped n k i' s' = unclippedFormula n k i' s')
    (s : Fin (k + 1)) :
    samplesUnclipped n k i s =
      1 / ((k : ℝ) + 1) * (∏ t ∈ Icc 1 (n - 1), (((s : ℕ) : ℝ) + t) / ((k : ℝ) + t + 1)) -
        1 / ((k : ℝ) + 1) * (∏ t ∈ Icc 1 (n - 1), 1 / ((k : ℝ) + t + 1)) *
          (∏ t ∈ Icc 1 (i - 1), (((s : ℕ) : ℝ) + t)) *
          ∑ s' ∈ Icc (s : ℕ) k, T n k i s' := by
  rw [tred_unfold n k i hin s]
  have h1 : ∀ j ∈ Ioc i n, ∑ s' : Fin (k + 1), samplesUnclipped n k j s' * coeffC s' i s =
      ∑ s' : Fin (k + 1), unclippedFormula n k j s' * coeffC s' i s := by
    intro j hj
    have := mem_Ioc.1 hj
    apply Finset.sum_congr rfl
    intro s' _
    rw [ih j this.1 this.2 s']
  rw [Finset.sum_congr rfl h1]
  have h2 : ∀ j, ∑ s' : Fin (k + 1), unclippedFormula n k j s' * coeffC s' i s =
      ∑ s' ∈ Icc (s : ℕ) k, unclippedFormula n k j s' * coeffC s' i s := by
    intro j
    rw [Fin.sum_univ_eq_sum_range (fun s' => unclippedFormula n k j s' * coeffC s' i s) (k + 1)]
    symm
    apply Finset.sum_subset
    · intro x hx
      simp only [mem_Icc, mem_range] at hx ⊢
      omega
    · intro x hx hx'
      simp only [mem_Icc, mem_range, not_and, not_le] at hx hx'
      have : x < (s : ℕ) := by omega
      rw [coeffC, if_neg (by omega)]
      simp
  simp only [h2]
  rw [Finset.sum_comm]
  have h3 : ∀ s' ∈ Icc (s : ℕ) k, ∑ j ∈ Ioc i n, unclippedFormula n k j s' * coeffC s' i s =
      (∏ t ∈ Icc 1 (i - 1), (((s : ℕ) : ℝ) + t)) /
        (((k : ℝ) + 1) * ∏ t ∈ Icc 1 (n - 1), ((k : ℝ) + t + 1)) * T n k i s' :=
    fun s' hs' => tred_sumT n k i s s' hi hin (mem_Icc.1 hs').1
  rw [Finset.sum_congr rfl h3, ← Finset.mul_sum]
  unfold coeffA
  have hpi : ∏ t ∈ Icc 1 (n - 1), 1 / ((k : ℝ) + t + 1) = 1 / ∏ t ∈ Icc 1 (n - 1), ((k : ℝ) + t + 1) := by
    rw [Finset.prod_div_distrib]
    simp
  rw [hpi]
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hpos : 0 < ∏ t ∈ Icc 1 (n - 1), ((k : ℝ) + t + 1) := by
    apply Finset.prod_pos
    intro t _
    positivity
  field_simp

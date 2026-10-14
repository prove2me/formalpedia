-- Prove2me | solution 1 for PoissonDepTrials.MixSqrt.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:13:54.468053+00:00
-- url     : https://prove2.me/submissions/cde162da-da11-4c01-bdc0-3b31f8fa5e53

import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Finset

namespace PoissonDepTrials.MixSqrt

lemma l31_seq (lam : ℝ) (hlam : 0 < lam) (N : ℕ) (a : ℕ → ℝ) (ha0 : a 0 ≤ 1)
    (hnn : ∀ j, 0 ≤ a j) (hle : ∀ j, a j ≤ 1)
    (hrec : ∀ j < N, ((j:ℝ)+1)/lam * a j ≤ a j - a (j+1)) :
    ∑ j ∈ range N, a j ≤ 2 * Real.sqrt lam := by
  have htel : ∑ j ∈ range N, ((j:ℝ)+1) * a j ≤ lam := by
    have h1 : ∑ j ∈ range N, ((j:ℝ)+1)/lam * a j ≤ ∑ j ∈ range N, (a j - a (j+1)) :=
      sum_le_sum (fun j hj => hrec j (mem_range.mp hj))
    rw [sum_range_sub'] at h1
    have h2 : ∑ j ∈ range N, ((j:ℝ)+1)/lam * a j = (∑ j ∈ range N, ((j:ℝ)+1) * a j) / lam := by
      rw [sum_div]; apply sum_congr rfl; intro j _; ring
    rw [h2, div_le_iff₀ hlam] at h1
    nlinarith [hnn N]
  set K := ⌊Real.sqrt lam⌋₊ with hK
  have hK1 : (0:ℝ) < (K:ℝ)+1 := by positivity
  have hpt : ∀ j ∈ range N, a j ≤ (if j < K then 1 else 0) + ((j:ℝ)+1) * a j / ((K:ℝ)+1) := by
    intro j _
    split_ifs with hj
    · have : 0 ≤ ((j:ℝ)+1) * a j / ((K:ℝ)+1) := by have := hnn j; positivity
      linarith [hle j]
    · push Not at hj
      rw [zero_add, le_div_iff₀ hK1]
      have : (K:ℝ) ≤ j := by exact_mod_cast hj
      nlinarith [hnn j]
  have hsum := sum_le_sum hpt
  rw [sum_add_distrib, ← sum_div] at hsum
  have hite : ∑ j ∈ range N, (if j < K then (1:ℝ) else 0) ≤ K := by
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
    have : (filter (fun j => j < K) (range N)).card ≤ K := by
      calc _ ≤ (range K).card := card_le_card (fun x hx => by simp at hx ⊢; exact hx.2)
        _ = K := card_range K
    exact_mod_cast this
  have hs := Real.sqrt_nonneg lam
  have hss := Real.sq_sqrt hlam.le
  have hKle : (K:ℝ) ≤ Real.sqrt lam := Nat.floor_le hs
  have hKlt : Real.sqrt lam < (K:ℝ) + 1 := Nat.lt_floor_add_one _
  have hfrac : (∑ j ∈ range N, ((j:ℝ)+1) * a j) / ((K:ℝ)+1) ≤ lam / ((K:ℝ)+1) :=
    div_le_div_of_nonneg_right htel hK1.le
  have hfin : (K:ℝ) + lam / ((K:ℝ)+1) ≤ 2 * Real.sqrt lam := by
    rw [← sub_nonneg]
    have : 2 * Real.sqrt lam - ((K:ℝ) + lam / ((K:ℝ)+1)) =
        (2 * Real.sqrt lam * ((K:ℝ)+1) - (K:ℝ)*((K:ℝ)+1) - lam) / ((K:ℝ)+1) := by
      field_simp; ring
    rw [this]; apply div_nonneg _ hK1.le
    nlinarith [mul_nonneg (sub_nonneg.2 hKlt.le) (sub_nonneg.2 (show (K:ℝ) + 1 - Real.sqrt lam ≤ 1 by linarith))]
  linarith

theorem l31_core (lam : ℝ) (w : ℕ) (hw : 1 ≤ w) (hlw : (w : ℝ) ≤ lam) :
    ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ * ∑ k ∈ Finset.range w, lam ^ k / (k.factorial : ℝ)
      ≤ 2 / Real.sqrt lam := by
  obtain ⟨n, rfl⟩ : ∃ n, w = n + 1 := ⟨w - 1, by omega⟩
  have hlam : 0 < lam := by have : (1:ℝ) ≤ ((n+1 : ℕ):ℝ) := by exact_mod_cast hw
                            linarith
  simp only [Nat.add_sub_cancel]
  set a : ℕ → ℝ := fun j => (n.descFactorial j : ℝ) / lam ^ j with ha
  have hQ : (n.factorial : ℝ) * (lam ^ (n+1))⁻¹ * ∑ k ∈ Finset.range (n+1), lam ^ k / (k.factorial : ℝ)
      = lam⁻¹ * ∑ j ∈ range (n+1), a j := by
    rw [← sum_range_reflect, mul_sum, mul_sum]
    apply sum_congr rfl
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    simp only [ha, Nat.add_sub_cancel]
    have hf : (n.factorial : ℝ) = ((n - j).factorial : ℝ) * (n.descFactorial j : ℝ) := by
      exact_mod_cast (Nat.factorial_mul_descFactorial hjn).symm
    have hp : lam ^ (n+1) = lam ^ (n - j) * lam ^ j * lam := by
      rw [← pow_add, Nat.sub_add_cancel hjn, pow_succ]
    rw [hf, hp]
    have : ((n - j).factorial : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hQ]
  have hnl : (n:ℝ) + 1 ≤ lam := by exact_mod_cast hlw
  have hS : ∑ j ∈ range (n+1), a j ≤ 2 * Real.sqrt lam := by
    apply l31_seq lam hlam (n+1) a
    · simp [ha]
    · intro j; simp only [ha]; positivity
    · intro j; simp only [ha]
      rw [div_le_one (by positivity)]
      calc (n.descFactorial j : ℝ) ≤ (n:ℝ) ^ j := by exact_mod_cast Nat.descFactorial_le_pow n j
        _ ≤ lam ^ j := pow_le_pow_left₀ (by positivity) (by linarith) j
    · intro j hj
      have hjn : j ≤ n := Nat.lt_succ_iff.mp hj
      simp only [ha]
      rw [Nat.descFactorial_succ]
      push_cast [Nat.cast_sub hjn]
      have hd : (0:ℝ) ≤ n.descFactorial j := by positivity
      rw [pow_succ]
      have hlj : 0 < lam ^ j := by positivity
      rw [div_mul_eq_mul_div, div_le_iff₀ hlam]
      field_simp
      nlinarith [mul_nonneg hd (sub_nonneg.2 hnl)]
  have hsq : 0 < Real.sqrt lam := Real.sqrt_pos.2 hlam
  calc lam⁻¹ * ∑ j ∈ range (n+1), a j ≤ lam⁻¹ * (2 * Real.sqrt lam) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = 2 / Real.sqrt lam := by
        have h2 : lam = Real.sqrt lam * Real.sqrt lam := (Real.mul_self_sqrt hlam.le).symm
        rw [eq_div_iff hsq.ne']; nth_rewrite 1 [h2]; field_simp


lemma l32_sumid (K : ℕ) : (∑ j ∈ range K, (j:ℝ)) * 2 = (K:ℝ) * ((K:ℝ) - 1) := by
  induction K with
  | zero => simp
  | succ m ih => rw [sum_range_succ, add_mul, ih]; push_cast; ring

lemma l32_seq (w lam : ℝ) (hw : 1 ≤ w) (hl : 0 < lam) (hlw : lam ≤ w) (b : ℕ → ℝ)
    (hb0 : b 0 = 1) (hnn : ∀ j, 0 ≤ b j) (hrec : ∀ j : ℕ, b (j+1) = b j * lam / (w + j + 1))
    (K : ℕ) (hK : 1 ≤ K) (N : ℕ) :
    ∑ j ∈ range N, b j ≤ ((K:ℝ)+1)/2 + w / K := by
  have hle1 : ∀ j, b j ≤ 1 := by
    intro j
    induction j with
    | zero => rw [hb0]
    | succ m ih =>
      rw [hrec]
      have hpos : (0:ℝ) < w + m + 1 := by positivity
      rw [div_le_one hpos]
      have : (0:ℝ) ≤ m := by positivity
      nlinarith [hnn m]
  have hinv : ∀ N, ∑ j ∈ range N, (j:ℝ) * b j + ((N:ℝ) + w) * b N ≤ w := by
    intro N
    induction N with
    | zero => simp [hb0]
    | succ m ih =>
      rw [sum_range_succ, hrec]
      have hpos : (0:ℝ) < w + m + 1 := by positivity
      have : ((((m+1 : ℕ):ℝ)) + w) * (b m * lam / (w + m + 1)) = lam * b m := by
        push_cast; field_simp; ring
      rw [this]
      nlinarith [hnn m]
  have hT : ∑ j ∈ range N, (j:ℝ) * b j ≤ w := by
    have := hinv N
    have : 0 ≤ ((N:ℝ) + w) * b N := mul_nonneg (by positivity) (hnn N)
    linarith
  have hKp : (0:ℝ) < K := by exact_mod_cast hK
  set g : ℕ → ℝ := fun j => if j < K then 1 - (j:ℝ)/K else 0 with hg
  have hgnn : ∀ j, 0 ≤ g j := by
    intro j; simp only [hg]; split_ifs with h
    · have : (j:ℝ) < K := by exact_mod_cast h
      rw [sub_nonneg, div_le_one hKp]; linarith
    · rfl
  have hpt : ∀ j ∈ range N, b j ≤ g j + (j:ℝ) * b j / K := by
    intro j _
    simp only [hg]
    split_ifs with h
    · have : (j:ℝ) < K := by exact_mod_cast h
      have e : 1 - (j:ℝ)/K + (j:ℝ) * b j / K - b j = (1 - b j) * (1 - (j:ℝ)/K) := by ring
      have h1 : 0 ≤ 1 - (j:ℝ)/K := by rw [sub_nonneg, div_le_one hKp]; linarith
      nlinarith [mul_nonneg (sub_nonneg.2 (hle1 j)) h1]
    · push Not at h
      have : (K:ℝ) ≤ j := by exact_mod_cast h
      rw [zero_add, le_div_iff₀ hKp]
      nlinarith [hnn j]
  have hsum := sum_le_sum hpt
  rw [sum_add_distrib, ← sum_div] at hsum
  have hgsum : ∑ j ∈ range N, g j ≤ ((K:ℝ)+1)/2 := by
    calc ∑ j ∈ range N, g j ≤ ∑ j ∈ range (K + N), g j := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro x hx; simp at hx ⊢; omega
          · intro i _ _; exact hgnn i
      _ = ∑ j ∈ range K, (1 - (j:ℝ)/K) := by
          rw [sum_range_add]
          have : ∑ x ∈ range N, g (K + x) = 0 := by
            apply sum_eq_zero; intro x _; simp [hg]
          rw [this, add_zero]
          apply sum_congr rfl; intro x hx; simp [hg, mem_range.mp hx]
      _ = ((K:ℝ)+1)/2 := by
          rw [sum_sub_distrib, ← sum_div, sum_const, card_range, nsmul_eq_mul, mul_one]
          have := l32_sumid K
          field_simp
          linarith
  have : (∑ j ∈ range N, (j:ℝ) * b j) / K ≤ w / K := div_le_div_of_nonneg_right hT hKp.le
  linarith

lemma l32_tsum (lam : ℝ) (hlam : 0 < lam) (w : ℕ) (hw : 1 ≤ w) (hlw : lam ≤ w) (b : ℕ → ℝ)
    (hb0 : b 0 = 1) (hnn : ∀ j, 0 ≤ b j) (hrec : ∀ j : ℕ, b (j+1) = b j * lam / ((w:ℝ) + j + 1)) :
    ∑' j, b j ≤ 2 * Real.sqrt w := by
  have hw1 : (1:ℝ) ≤ w := by exact_mod_cast hw
  have key : ∀ K : ℕ, 1 ≤ K → ((K:ℝ)+1)/2 + w / K ≤ 2 * Real.sqrt w →
      ∑' j, b j ≤ 2 * Real.sqrt w := by
    intro K hK hb
    apply Real.tsum_le_of_sum_range_le hnn
    intro N
    exact (l32_seq w lam hw1 hlam hlw b hb0 hnn hrec K hK N).trans hb
  rcases (show w = 1 ∨ w = 2 ∨ 3 ≤ w by omega) with h | h | h
  · subst h; apply key 1 le_rfl; norm_num
  · subst h; apply key 2 (by norm_num)
    have : (1.25:ℝ) ≤ Real.sqrt 2 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    norm_num; linarith
  · have hw3 : (3:ℝ) ≤ w := by exact_mod_cast h
    set s := Real.sqrt w with hs
    set t := Real.sqrt (2 * w) with ht
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have ht0 : 0 ≤ t := Real.sqrt_nonneg _
    have hss : s ^ 2 = w := Real.sq_sqrt (by linarith)
    have htt : t ^ 2 = 2 * w := Real.sq_sqrt (by linarith)
    have htpos : 0 < t := by nlinarith
    set K := ⌈t⌉₊ with hK
    have hK1 : t ≤ K := Nat.le_ceil t
    have hK2 : (K:ℝ) < t + 1 := Nat.ceil_lt_add_one ht0
    have hKpos : (0:ℝ) < K := lt_of_lt_of_le htpos hK1
    apply key K (by exact_mod_cast hKpos)
    have h1 : w / K ≤ w / t := div_le_div_of_nonneg_left (by linarith) htpos hK1
    have h2 : w / t = t / 2 := by
      rw [div_eq_div_iff htpos.ne' (by norm_num)]; nlinarith
    have hs17 : 1.732 ≤ s := by nlinarith
    have hts : t ≤ 1.4143 * s := by nlinarith
    linarith

theorem l32_core (lam : ℝ) (hlam : 0 < lam) (w : ℕ) (hw : 1 ≤ w) (hlw : lam ≤ w) :
    ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ * ∑' k : ℕ, lam ^ (k + w) / ((k + w).factorial : ℝ)
      ≤ 2 / Real.sqrt w := by
  set b : ℕ → ℝ := fun k => lam ^ k * (w.factorial : ℝ) / ((k + w).factorial : ℝ) with hb
  have hwpos : (0:ℝ) < w := by exact_mod_cast hw
  have hterm : ∀ k : ℕ, ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ * (lam ^ (k + w) / ((k + w).factorial : ℝ))
      = b k / w := by
    intro k
    simp only [hb]
    have hf : (w.factorial : ℝ) = w * ((w-1).factorial : ℝ) := by
      exact_mod_cast (Nat.mul_factorial_pred (by omega : w ≠ 0)).symm
    rw [hf, pow_add]
    have : ((k + w).factorial : ℝ) ≠ 0 := by positivity
    have : lam ^ w ≠ 0 := by positivity
    field_simp
  rw [← tsum_mul_left]
  simp_rw [hterm]
  rw [tsum_div_const]
  have hT : ∑' j, b j ≤ 2 * Real.sqrt w := by
    apply l32_tsum lam hlam w hw hlw b
    · simp [hb, Nat.factorial_ne_zero]
    · intro j; simp only [hb]; positivity
    · intro j; simp only [hb]
      have e : (j + 1 + w).factorial = (j + w + 1) * (j + w).factorial := by
        rw [show j + 1 + w = (j + w) + 1 by ring]; exact Nat.factorial_succ _
      rw [e, pow_succ]; push_cast
      have : ((j + w).factorial : ℝ) ≠ 0 := by positivity
      have : (j:ℝ) + w + 1 ≠ 0 := by positivity
      field_simp; ring
  have hsq : 0 < Real.sqrt w := Real.sqrt_pos.2 hwpos
  have h2 : (w:ℝ) = Real.sqrt w * Real.sqrt w := (Real.mul_self_sqrt hwpos.le).symm
  calc (∑' j, b j) / w ≤ 2 * Real.sqrt w / w := div_le_div_of_nonneg_right hT hwpos.le
    _ = 2 / Real.sqrt w := by
        rw [div_eq_div_iff hwpos.ne' hsq.ne', mul_assoc, ← h2]


lemma M_nonneg' (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M) : 0 ≤ M := (abs_nonneg _).trans (hM 0)

lemma exp_tsum' (x : ℝ) : ∑' n : ℕ, x ^ n / (n.factorial : ℝ) = Real.exp x := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

lemma summ_bdd (lam : ℝ) (f : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |f k| ≤ M) :
    Summable (fun k => lam ^ k / (k.factorial:ℝ) * f k) := by
  refine Summable.of_norm_bounded ((Real.summable_pow_div_factorial |lam|).mul_right M) (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast]
  exact mul_le_mul_of_nonneg_left (hM k) (by positivity)

lemma pe_eq (lam : ℝ) (h : ℕ → ℝ) :
    poissonExp lam h = Real.exp (-lam) * ∑' k, lam ^ k / (k.factorial:ℝ) * h k := by
  unfold poissonExp
  rw [← tsum_mul_left]
  apply tsum_congr; intro k; ring

lemma pe_abs_le (lam : ℝ) (hlam : 0 ≤ lam) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M) :
    |poissonExp lam h| ≤ M := by
  rw [pe_eq]
  have hs := summ_bdd lam h M hM
  have hs2 : Summable (fun k => lam ^ k / (k.factorial:ℝ) * M) :=
    (Real.summable_pow_div_factorial lam).mul_right M
  have hsM : ∑' k, lam ^ k / (k.factorial:ℝ) * M = Real.exp lam * M := by
    rw [tsum_mul_right, exp_tsum']
  have hb : |∑' k, lam ^ k / (k.factorial:ℝ) * h k| ≤ Real.exp lam * M := by
    rw [← hsM, ← Real.norm_eq_abs]
    refine tsum_of_norm_bounded (f := fun k => lam ^ k / (k.factorial:ℝ) * h k) hs2.hasSum (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast, abs_of_nonneg hlam]
    exact mul_le_mul_of_nonneg_left (hM k) (by positivity)
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-lam) * |∑' k, lam ^ k / (k.factorial:ℝ) * h k|
      ≤ Real.exp (-lam) * (Real.exp lam * M) := mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = M := by rw [← mul_assoc, ← Real.exp_add]; simp

lemma g_summable (lam : ℝ) (hlam : 0 ≤ lam) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M) :
    Summable (fun k => (h k - poissonExp lam h) * lam ^ k / (k.factorial : ℝ)) := by
  have hP := pe_abs_le lam hlam h M hM
  have := summ_bdd lam (fun k => h k - poissonExp lam h) (2 * M) (fun k => by
    have := hM k
    calc |h k - poissonExp lam h| ≤ |h k| + |poissonExp lam h| := abs_sub _ _
      _ ≤ 2 * M := by linarith)
  refine this.congr (fun k => ?_)
  ring

lemma g_tsum_zero (lam : ℝ) (hlam : 0 ≤ lam) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M) :
    ∑' k, (h k - poissonExp lam h) * lam ^ k / (k.factorial : ℝ) = 0 := by
  have hs := summ_bdd lam h M hM
  have hs2 := (Real.summable_pow_div_factorial lam).mul_left (poissonExp lam h)
  have e : (fun k => (h k - poissonExp lam h) * lam ^ k / (k.factorial : ℝ)) =
      fun k => lam ^ k / (k.factorial:ℝ) * h k - poissonExp lam h * (lam ^ k / (k.factorial:ℝ)) := by
    funext k; ring
  rw [e, hs.tsum_sub hs2, tsum_mul_left, exp_tsum']
  have hP := pe_eq lam h
  have : ∑' k, lam ^ k / (k.factorial:ℝ) * h k = Real.exp lam * poissonExp lam h := by
    rw [hP, ← mul_assoc, ← Real.exp_add]; simp
  rw [this]; ring

lemma stein_tail (lam : ℝ) (hlam : 0 ≤ lam) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M) (w : ℕ) :
    ∑ k ∈ range w, (h k - poissonExp lam h) * lam ^ k / (k.factorial : ℝ) =
      -∑' k, (h (k + w) - poissonExp lam h) * lam ^ (k + w) / ((k + w).factorial : ℝ) := by
  have hs := g_summable lam hlam h M hM
  have := hs.sum_add_tsum_nat_add w
  rw [g_tsum_zero lam hlam h M hM] at this
  linarith

theorem l33_core (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M) :
    ∀ w : ℕ, 1 ≤ w → |stein lam h w| ≤ 4 * M * min (1 / Real.sqrt lam) 1 := by
  intro w hw
  have hM0 := M_nonneg' h M hM
  have hP := pe_abs_le lam hlam.le h M hM
  have hg2 : ∀ k, |h k - poissonExp lam h| ≤ 2 * M := fun k => by
    have := hM k
    calc |h k - poissonExp lam h| ≤ |h k| + |poissonExp lam h| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  have hc0 : (0:ℝ) ≤ ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ := by positivity
  unfold stein
  rw [abs_neg, abs_mul, abs_of_nonneg hc0]
  have hsl := Real.sqrt_pos.2 hlam
  rcases le_or_gt (w:ℝ) lam with hwl | hwl
  · -- head form
    have hA := l31_core lam w hw hwl
    have hb : |∑ k ∈ range w, (h k - poissonExp lam h) * lam ^ k / (k.factorial : ℝ)| ≤
        2 * M * ∑ k ∈ range w, lam ^ k / (k.factorial : ℝ) := by
      rw [mul_sum]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun k _ => ?_))
      rw [mul_div_assoc, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ lam ^ k / (k.factorial : ℝ))]
      exact mul_le_mul_of_nonneg_right (hg2 k) (by positivity)
    have hl1 : 1 ≤ lam := le_trans (by exact_mod_cast hw) hwl
    have hmin : min (1 / Real.sqrt lam) 1 = 1 / Real.sqrt lam := by
      apply min_eq_left
      rw [div_le_one hsl]; rw [Real.le_sqrt (by norm_num) hlam.le]; simpa using hl1
    rw [hmin]
    calc ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ * |∑ k ∈ range w, (h k - poissonExp lam h) * lam ^ k / (k.factorial : ℝ)|
        ≤ ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ * (2 * M * ∑ k ∈ range w, lam ^ k / (k.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left hb hc0
      _ = 2 * M * (((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ * ∑ k ∈ range w, lam ^ k / (k.factorial : ℝ)) := by ring
      _ ≤ 2 * M * (2 / Real.sqrt lam) := mul_le_mul_of_nonneg_left hA (by positivity)
      _ = 4 * M * (1 / Real.sqrt lam) := by ring
  · -- tail form
    have hB := l32_core lam hlam w hw hwl.le
    rw [stein_tail lam hlam.le h M hM w, abs_neg]
    have hs : Summable (fun k : ℕ => lam ^ (k + w) / ((k + w).factorial : ℝ)) :=
      (summable_nat_add_iff w).2 (Real.summable_pow_div_factorial lam)
    have hb : |∑' k, (h (k + w) - poissonExp lam h) * lam ^ (k + w) / ((k + w).factorial : ℝ)| ≤
        2 * M * ∑' k : ℕ, lam ^ (k + w) / ((k + w).factorial : ℝ) := by
      rw [← tsum_mul_left, ← Real.norm_eq_abs]
      refine tsum_of_norm_bounded
        (f := fun k => (h (k + w) - poissonExp lam h) * lam ^ (k + w) / ((k + w).factorial : ℝ))
        (hs.mul_left (2 * M)).hasSum (fun k => ?_)
      rw [Real.norm_eq_abs, mul_div_assoc, abs_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ lam ^ (k + w) / ((k + w).factorial : ℝ))]
      exact mul_le_mul_of_nonneg_right (hg2 _) (by positivity)
    have hw1 : (1:ℝ) ≤ w := by exact_mod_cast hw
    have hsw := Real.sqrt_pos.2 (by linarith : (0:ℝ) < w)
    have hmin : 1 / Real.sqrt w ≤ min (1 / Real.sqrt lam) 1 := by
      apply le_min
      · exact one_div_le_one_div_of_le hsl (Real.sqrt_le_sqrt hwl.le)
      · rw [div_le_one hsw, Real.le_sqrt (by norm_num) (by linarith)]; simpa using hw1
    calc ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ * |∑' k, (h (k + w) - poissonExp lam h) * lam ^ (k + w) / ((k + w).factorial : ℝ)|
        ≤ ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ * (2 * M * ∑' k : ℕ, lam ^ (k + w) / ((k + w).factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left hb hc0
      _ = 2 * M * (((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ * ∑' k : ℕ, lam ^ (k + w) / ((k + w).factorial : ℝ)) := by ring
      _ ≤ 2 * M * (2 / Real.sqrt w) := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = 4 * M * (1 / Real.sqrt w) := by ring
      _ ≤ 4 * M * min (1 / Real.sqrt lam) 1 := mul_le_mul_of_nonneg_left hmin (by positivity)

end PoissonDepTrials.MixSqrt

open PoissonDepTrials.MixSqrt


theorem solution (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M) :
    ∀ w : ℕ, 1 ≤ w → |stein lam h w| ≤ 4 * M * min (1 / Real.sqrt lam) 1 := by
  exact l33_core lam hlam h M hM

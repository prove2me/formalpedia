-- Prove2me | solution 1 for PoissonDepTrials.MixInv.bound_4_19
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:20:28.545639+00:00
-- url     : https://prove2.me/submissions/ef706738-3efb-4a56-a0f9-4c78747fd11c

import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Finset

namespace PoissonDepTrials.MixInv

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

theorem stein_eq_core (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (w : ℕ) :
    (w : ℝ) * stein lam h w - lam * stein lam h (w + 1) = h w - poissonExp lam h := by
  have hl : lam ≠ 0 := hlam.ne'
  cases w with
  | zero => simp [stein]; field_simp
  | succ k =>
    simp only [stein]
    rw [sum_range_succ _ (k + 1)]
    simp only [Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    field_simp
    ring

theorem stein_solution_core (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ)
    (hM : ∀ k, |h k| ≤ M) :
    (∀ w : ℕ, (w : ℝ) * stein lam h w - lam * stein lam h (w + 1) = h w - poissonExp lam h) ∧
    (∀ w : ℕ, 1 ≤ w → stein lam h w = ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ *
      ∑' k : ℕ, (h (k + w) - poissonExp lam h) * lam ^ (k + w) / ((k + w).factorial : ℝ)) := by
  refine ⟨fun w => stein_eq_core lam hlam h w, fun w _ => ?_⟩
  unfold stein
  rw [stein_tail lam hlam.le h M hM w]
  ring


def Sc (n : ℕ) (a : ℤ) (c : ℕ → ℕ) (T : ℤ) : ℕ :=
  ∑ k ∈ (Icc 1 n).filter (fun k : ℕ => a ≤ (k:ℤ) ∧ (k:ℤ) ≤ T), c k

lemma sum_eqT {M : Type*} [AddCommMonoid M] (n : ℕ) (T : ℤ) (g : ℕ → M) :
    ∑ k ∈ (Icc 1 n).filter (fun k : ℕ => (k:ℤ) = T), g k =
      if 1 ≤ T ∧ T ≤ n then g T.toNat else 0 := by
  split_ifs with hT
  · have : (Icc 1 n).filter (fun k : ℕ => (k:ℤ) = T) = {T.toNat} := by
      ext k; simp only [mem_filter, mem_Icc, mem_singleton]; omega
    rw [this, sum_singleton]
  · have : (Icc 1 n).filter (fun k : ℕ => (k:ℤ) = T) = ∅ := by
      ext k; simp only [mem_filter, mem_Icc, Finset.notMem_empty, iff_false]; omega
    rw [this, sum_empty]

lemma Sc_succ (n : ℕ) (a : ℤ) (c : ℕ → ℕ) (T : ℤ) (hT : a - 1 ≤ T) :
    Sc n a c (T + 1) = Sc n a c T + if 1 ≤ T + 1 ∧ T + 1 ≤ n then c (T + 1).toNat else 0 := by
  unfold Sc
  rw [← sum_eqT, ← sum_union]
  · congr 1; ext k; simp only [mem_filter, mem_union, mem_Icc]; omega
  · rw [disjoint_left]; intro k h1 h2; simp only [mem_filter] at h1 h2; omega

lemma Sc_empty (n : ℕ) (a : ℤ) (c : ℕ → ℕ) : Sc n a c (a - 1) = 0 := by
  unfold Sc
  apply sum_eq_zero; intro k hk; simp only [mem_filter] at hk; omega

lemma tele (n : ℕ) (a : ℤ) (c : ℕ → ℕ) (hc : ∀ k, c k ≤ 1) (f : ℕ → ℝ) (V : ℕ) (L : ℕ) :
    f (V + Sc n a c (a - 1 + L) + 1) - f (V + 1) =
    ∑ j ∈ (Icc 1 n).filter (fun j : ℕ => a ≤ (j:ℤ) ∧ (j:ℤ) ≤ a - 1 + L),
      (c j : ℝ) * delta f (V + Sc n a c ((j:ℤ) - 1) + 1) := by
  induction L with
  | zero =>
    simp only [CharP.cast_eq_zero, add_zero, Sc_empty]
    rw [sum_eq_zero]
    · simp
    · intro k hk; simp only [mem_filter] at hk; omega
  | succ L ih =>
    have hset : (Icc 1 n).filter (fun j : ℕ => a ≤ (j:ℤ) ∧ (j:ℤ) ≤ a - 1 + ((L+1:ℕ):ℤ)) =
       (Icc 1 n).filter (fun j : ℕ => a ≤ (j:ℤ) ∧ (j:ℤ) ≤ a - 1 + L) ∪
         (Icc 1 n).filter (fun j : ℕ => (j:ℤ) = a - 1 + L + 1) := by
      ext k; simp only [mem_filter, mem_union, mem_Icc]; push_cast; omega
    have hdisj : Disjoint ((Icc 1 n).filter (fun j : ℕ => a ≤ (j:ℤ) ∧ (j:ℤ) ≤ a - 1 + L))
         ((Icc 1 n).filter (fun j : ℕ => (j:ℤ) = a - 1 + L + 1)) := by
      rw [disjoint_left]; intro k h1 h2; simp only [mem_filter] at h1 h2; omega
    rw [hset, sum_union hdisj, ← ih, sum_eqT]
    have e1 : a - 1 + ((L + 1 : ℕ) : ℤ) = a - 1 + L + 1 := by push_cast; ring
    rw [e1, Sc_succ n a c _ (by omega)]
    split_ifs with hT
    · have e2 : (((a - 1 + L + 1).toNat : ℕ) : ℤ) - 1 = a - 1 + L := by omega
      rw [e2]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hc (a - 1 + L + 1).toNat) with h0 | h1
      · rw [h0]; simp
      · rw [h1]; simp only [delta]; push_cast
        have : V + (Sc n a c (a - 1 + ↑L) + 1) + 1 = V + Sc n a c (a - 1 + ↑L) + 1 + 1 := by ring
        rw [this]; ring
    · simp

lemma W_split {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (i : ℕ) (ω : Ω) :
    W n X ω = V n m X i ω + Sc n ((i:ℤ) - m) (fun k => X k ω) ((i:ℤ) + m) := by
  unfold W V Sc
  rw [← sum_filter_add_sum_filter_not (Icc 1 n) (fun k : ℕ => m < Int.natAbs ((k:ℤ) - i))]
  congr 1
  apply sum_congr _ (fun _ _ => rfl)
  apply filter_congr; intro k _; omega

lemma Y_eq {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (i : ℕ) (t : ℤ) (ω : Ω) :
    Y n m X i t ω = V n m X i ω + Sc n ((i:ℤ) - m) (fun k => X k ω) t := rfl

lemma Y'_eq {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (i : ℕ) (t : ℤ) (ω : Ω) :
    Y' n m X i t ω = V n m X i ω + Sc n ((i:ℤ) - m) (fun k => if k = i then 0 else X k ω) t := by
  unfold Y' Sc
  congr 1
  rw [sum_filter, sum_filter]
  apply sum_congr rfl; intro k _
  by_cases hk : k = i
  · simp [hk]
  · simp [hk]

lemma Sc_split (n : ℕ) (a : ℤ) (x : ℕ → ℕ) (T : ℤ) (i : ℕ) (hi : i ∈ Icc 1 n)
    (hai : a ≤ i) (hiT : (i:ℤ) ≤ T) :
    Sc n a x T = x i + Sc n a (fun k => if k = i then 0 else x k) T := by
  unfold Sc
  have : ∀ k, x k = (if k = i then 0 else x k) + (if i = k then x k else 0) := by
    intro k; by_cases hk : k = i
    · subst hk; simp
    · simp [hk, Ne.symm hk]
  conv_lhs => rw [sum_congr rfl (fun k _ => this k)]
  rw [sum_add_distrib, sum_ite_eq, if_pos]
  · ring
  · simp only [mem_filter]; exact ⟨hi, hai, hiT⟩

lemma ptA {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (f : ℕ → ℝ) (ω : Ω) (hx : ∀ k, X k ω ≤ 1)
    (i : ℕ) (hi : i ∈ Icc 1 n) :
    (X i ω : ℝ) * f (W n X ω) = (X i ω : ℝ) * f (V n m X i ω + 1) +
      ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
        (X i ω : ℝ) * X j ω * delta f (Y' n m X i ((j : ℤ) - 1) ω + 1) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hx i) with h0 | h1
  · simp [h0]
  · rw [h1, W_split n m X i ω, Sc_split n _ _ _ i hi (by omega) (by omega), h1]
    set x' : ℕ → ℕ := fun k => if k = i then 0 else X k ω with hx'
    have hc : ∀ k, x' k ≤ 1 := by
      intro k; simp only [hx']; split_ifs
      · omega
      · exact hx k
    have ht := tele n ((i:ℤ) - m) x' hc f (V n m X i ω) (2*m+1)
    have e : (i:ℤ) - m - 1 + ((2*m+1 : ℕ):ℤ) = i + m := by push_cast; ring
    rw [e] at ht
    simp only [Nat.cast_one, one_mul]
    have e2 : V n m X i ω + (1 + Sc n (↑i - ↑m) x' (↑i + ↑m)) = V n m X i ω + Sc n (↑i - ↑m) x' (↑i + ↑m) + 1 := by ring
    rw [e2, ← sub_eq_iff_eq_add', ht, sum_filter, sum_filter]
    apply sum_congr rfl; intro j _
    rw [Y'_eq]
    by_cases hji : j = i
    · subst hji; simp [hx']
    · have : x' j = X j ω := by simp [hx', hji]
      rw [this]
      have hji' : (i:ℤ) - j ≠ 0 := by omega
      by_cases hc1 : (i:ℤ) - m ≤ j ∧ (j:ℤ) ≤ i + m
      · rw [if_pos hc1, if_pos]
        rw [abs_pos, abs_le]; exact ⟨hji', by omega, by omega⟩
      · rw [if_neg hc1, if_neg]
        rw [abs_pos, abs_le]; omega

lemma ptB {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (f : ℕ → ℝ) (ω : Ω) (hx : ∀ k, X k ω ≤ 1)
    (i : ℕ) :
    f (W n X ω + 1) = f (V n m X i ω + 1) +
      ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
        (X j ω : ℝ) * delta f (Y n m X i ((j : ℤ) - 1) ω + 1) := by
  have ht := tele n ((i:ℤ) - m) (fun k => X k ω) hx f (V n m X i ω) (2*m+1)
  have e : (i:ℤ) - m - 1 + ((2*m+1 : ℕ):ℤ) = i + m := by push_cast; ring
  rw [e] at ht
  rw [W_split n m X i ω, ← sub_eq_iff_eq_add', ht]
  apply sum_congr _ (fun _ _ => rfl)
  apply filter_congr; intro j _; rw [abs_le]; omega

lemma sub_le_n (n : ℕ) (x : ℕ → ℕ) (hx : ∀ k, x k ≤ 1) (s : Finset ℕ) (hs : s ⊆ Icc 1 n) :
    ∑ k ∈ s, x k ≤ n := by
  calc ∑ k ∈ s, x k ≤ ∑ k ∈ s, 1 := sum_le_sum (fun k _ => hx k)
    _ = s.card := by simp
    _ ≤ (Icc 1 n).card := card_le_card hs
    _ = n := by simp

lemma V_le {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (ω : Ω) (hx : ∀ k, X k ω ≤ 1) (i : ℕ) :
    V n m X i ω ≤ n := sub_le_n n (fun k => X k ω) hx _ (filter_subset _ _)

lemma Y_le {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (ω : Ω) (hx : ∀ k, X k ω ≤ 1) (i : ℕ) (t : ℤ) :
    Y n m X i t ω ≤ 2 * n := by
  have := V_le n m X ω hx i
  have := sub_le_n n (fun k => X k ω) hx _ (filter_subset (fun k : ℕ => (i : ℤ) - m ≤ k ∧ (k : ℤ) ≤ t) (Icc 1 n))
  unfold Y; omega

lemma Y'_le {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (ω : Ω) (hx : ∀ k, X k ω ≤ 1) (i : ℕ) (t : ℤ) :
    Y' n m X i t ω ≤ 2 * n := by
  have := V_le n m X ω hx i
  have := sub_le_n n (fun k => X k ω) hx _ (filter_subset (fun k : ℕ => k ≠ i ∧ (i : ℤ) - m ≤ k ∧ (k : ℤ) ≤ t) (Icc 1 n))
  unfold Y'; omega

lemma W_le {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℕ) (ω : Ω) (hx : ∀ k, X k ω ≤ 1) :
    W n X ω ≤ n := sub_le_n n (fun k => X k ω) hx _ (subset_refl _)

lemma fb_le (f : ℕ → ℝ) (N k : ℕ) (hk : k < N) : |f k| ≤ ∑ j ∈ range N, |f j| :=
  single_le_sum (f := fun j => |f j|) (fun j _ => abs_nonneg _) (mem_range.mpr hk)

lemma cast_le_one' (a : ℕ) (h : a ≤ 1) : |(a:ℝ)| ≤ 1 := by
  rw [abs_of_nonneg (by positivity)]; exact_mod_cast h

lemma integ_bdd {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ᵐ ω ∂P, |g ω| ≤ C) : Integrable g P :=
  Integrable.of_bound hg.aestronglyMeasurable C (by filter_upwards [hC] with ω h; simpa using h)

lemma meas_V {Ω : Type*} [MeasurableSpace Ω] (n m : ℕ) (X : ℕ → Ω → ℕ) (hX : ∀ i, Measurable (X i)) (i : ℕ) :
    Measurable (V n m X i) := by
  unfold V; apply Finset.measurable_sum; intro k _; exact hX k

lemma meas_Y {Ω : Type*} [MeasurableSpace Ω] (n m : ℕ) (X : ℕ → Ω → ℕ) (hX : ∀ i, Measurable (X i)) (i : ℕ) (t : ℤ) :
    Measurable (Y n m X i t) := by
  unfold Y V; apply Measurable.add <;> apply Finset.measurable_sum <;> intro k _ <;> exact hX k

lemma meas_Y' {Ω : Type*} [MeasurableSpace Ω] (n m : ℕ) (X : ℕ → Ω → ℕ) (hX : ∀ i, Measurable (X i)) (i : ℕ) (t : ℤ) :
    Measurable (Y' n m X i t) := by
  unfold Y' V; apply Measurable.add <;> apply Finset.measurable_sum <;> intro k _ <;> exact hX k

lemma meas_W {Ω : Type*} [MeasurableSpace Ω] (n : ℕ) (X : ℕ → Ω → ℕ) (hX : ∀ i, Measurable (X i)) :
    Measurable (W n X) := by
  unfold W; apply Finset.measurable_sum; intro k _; exact hX k

lemma mcast {Ω : Type*} [MeasurableSpace Ω] (g : Ω → ℕ) (hg : Measurable g) (F : ℕ → ℝ) :
    Measurable (fun ω => F (g ω)) := (measurable_from_top (f := F)).comp hg

theorem basic_identity_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (m : ℕ) (f : ℕ → ℝ) :
    ∫ ω, ((W n X ω : ℝ) * f (W n X ω) - lam P n X * f (W n X ω + 1)) ∂P =
      (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
          ∫ ω, (X i ω : ℝ) * X j ω * delta f (Y' n m X i ((j : ℤ) - 1) ω + 1) ∂P)
      + (∑ i ∈ Finset.Icc 1 n, ∫ ω, ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1) ∂P)
      - ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
          prob P X i * ∫ ω, (X j ω : ℝ) * delta f (Y n m X i ((j : ℤ) - 1) ω + 1) ∂P := by
  obtain ⟨hXm, _, hX1⟩ := hX
  have hgood : ∀ᵐ ω ∂P, ∀ k, X k ω ≤ 1 := ae_all_iff.mpr hX1
  set Fb := ∑ j ∈ range (2 * n + 3), |f j| with hFb
  have hF : ∀ k, k < 2 * n + 3 → |f k| ≤ Fb := fun k hk => fb_le f _ k hk
  have hD : ∀ y, y ≤ 2 * n → |delta f (y + 1)| ≤ 2 * Fb := by
    intro y hy; unfold delta
    have h1 := hF (y + 1 + 1) (by omega); have h2 := hF (y + 1) (by omega)
    calc |f (y + 1 + 1) - f (y + 1)| ≤ |f (y + 1 + 1)| + |f (y + 1)| := abs_sub _ _
      _ ≤ 2 * Fb := by linarith
  have iA : ∀ i j : ℕ, Integrable (fun ω => (X i ω : ℝ) * X j ω * delta f (Y' n m X i ((j : ℤ) - 1) ω + 1)) P := by
    intro i j
    refine integ_bdd P _ (((mcast _ (hXm i) _).mul (mcast _ (hXm j) _)).mul (mcast _ (meas_Y' n m X hXm i _) (fun y => delta f (y + 1)))) (2 * Fb) ?_
    filter_upwards [hgood] with ω hx
    rw [abs_mul, abs_mul]
    have := hD _ (Y'_le n m X ω hx i ((j:ℤ) - 1))
    have a1 := cast_le_one' _ (hx i); have a2 := cast_le_one' _ (hx j)
    calc |(X i ω : ℝ)| * |(X j ω : ℝ)| * |delta f (Y' n m X i (↑j - 1) ω + 1)| ≤ 1 * 1 * (2 * Fb) := by
          gcongr
      _ = 2 * Fb := by ring
  have iC : ∀ i j : ℕ, Integrable (fun ω => (X j ω : ℝ) * delta f (Y n m X i ((j : ℤ) - 1) ω + 1)) P := by
    intro i j
    refine integ_bdd P _ ((mcast _ (hXm j) _).mul (mcast _ (meas_Y n m X hXm i _) (fun y => delta f (y + 1)))) (2 * Fb) ?_
    filter_upwards [hgood] with ω hx
    rw [abs_mul]
    have := hD _ (Y_le n m X ω hx i ((j:ℤ) - 1))
    have a2 := cast_le_one' _ (hx j)
    calc |(X j ω : ℝ)| * |delta f (Y n m X i (↑j - 1) ω + 1)| ≤ 1 * (2 * Fb) := by
          gcongr
      _ = 2 * Fb := by ring
  have iB : ∀ i : ℕ, Integrable (fun ω => ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1)) P := by
    intro i
    refine integ_bdd P _ (((mcast _ (hXm i) _).sub measurable_const).mul (mcast _ (meas_V n m X hXm i) (fun y => f (y + 1)))) ((1 + |prob P X i|) * Fb) ?_
    filter_upwards [hgood] with ω hx
    rw [abs_mul]
    have := hF (V n m X i ω + 1) (by have := V_le n m X ω hx i; omega)
    have a1 := cast_le_one' _ (hx i)
    have : |(X i ω : ℝ) - prob P X i| ≤ 1 + |prob P X i| := (abs_sub _ _).trans (by linarith)
    gcongr
  -- pointwise identity
  have hpt : ∀ᵐ ω ∂P, ((W n X ω : ℝ) * f (W n X ω) - lam P n X * f (W n X ω + 1)) =
      (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
          (X i ω : ℝ) * X j ω * delta f (Y' n m X i ((j : ℤ) - 1) ω + 1))
      + (∑ i ∈ Finset.Icc 1 n, ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1))
      - ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
          prob P X i * ((X j ω : ℝ) * delta f (Y n m X i ((j : ℤ) - 1) ω + 1)) := by
    filter_upwards [hgood] with ω hx
    have hW : (W n X ω : ℝ) = ∑ i ∈ Icc 1 n, (X i ω : ℝ) := by unfold W; push_cast; rfl
    rw [hW, lam, sum_mul, sum_mul]
    rw [sum_congr rfl (fun i hi => ptA n m X f ω hx i hi)]
    rw [sum_congr rfl (fun i _ => congrArg (fun z => prob P X i * z) (ptB n m X f ω hx i))]
    simp only [mul_add, sum_add_distrib, mul_sum, sub_mul]
    rw [sum_sub_distrib]
    ring
  rw [integral_congr_ae hpt]
  rw [integral_sub, integral_add, integral_finset_sum, integral_finset_sum, integral_finset_sum]
  · congr 1; congr 1
    · apply sum_congr rfl; intro i _; rw [integral_finset_sum]; intro j _; exact iA i j
    · apply sum_congr rfl; intro i _; rw [integral_finset_sum]
      · apply sum_congr rfl; intro j _; rw [integral_const_mul]
      · intro j _; exact (iC i j).const_mul _
  · intro i _; exact integrable_finset_sum _ (fun j _ => (iC i j).const_mul _)
  · intro i _; exact iB i
  · intro i _; exact integrable_finset_sum _ (fun j _ => iA i j)
  · exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => iA i j))
  · exact integrable_finset_sum _ (fun i _ => iB i)
  · exact (integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => iA i j))).add
      (integrable_finset_sum _ (fun i _ => iB i))
  · exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => (iC i j).const_mul _))

theorem identity_2_6_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (hlam : 0 < lam P n X) (m : ℕ) (h : ℕ → ℝ) (M : ℝ)
    (hM : ∀ k, |h k| ≤ M) :
    ∫ ω, h (W n X ω) ∂P = poissonExp (lam P n X) h
      + (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
          ∫ ω, (X i ω : ℝ) * X j ω * delta (stein (lam P n X) h) (Y' n m X i ((j : ℤ) - 1) ω + 1) ∂P)
      + (∑ i ∈ Finset.Icc 1 n,
          ∫ ω, ((X i ω : ℝ) - prob P X i) * stein (lam P n X) h (V n m X i ω + 1) ∂P)
      - ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
          prob P X i * ∫ ω, (X j ω : ℝ) * delta (stein (lam P n X) h) (Y n m X i ((j : ℤ) - 1) ω + 1) ∂P := by
  have hb := basic_identity_core P n X hX m (stein (lam P n X) h)
  have he : ∀ ω, ((W n X ω : ℝ) * stein (lam P n X) h (W n X ω) - lam P n X * stein (lam P n X) h (W n X ω + 1))
      = h (W n X ω) - poissonExp (lam P n X) h := fun ω => stein_eq_core _ hlam h _
  simp only [he] at hb
  have hi : Integrable (fun ω => h (W n X ω)) P :=
    integ_bdd P _ (mcast _ (meas_W n X hX.1) h) M (ae_of_all _ (fun ω => hM _))
  rw [integral_sub hi (integrable_const _), integral_const] at hb
  simp only [probReal_univ, smul_eq_mul, one_mul] at hb
  linarith

lemma stein_eq (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (w : ℕ) :
    (w : ℝ) * stein lam h w - lam * stein lam h (w + 1) = h w - poissonExp lam h := by
  have hl : lam ≠ 0 := hlam.ne'
  cases w with
  | zero => simp [stein]; field_simp
  | succ n =>
    unfold stein
    simp only [Nat.add_sub_cancel]
    rw [sum_range_succ _ (n + 1), Nat.factorial_succ]
    set A := ∑ k ∈ range (n + 1), (h k - poissonExp lam h) * lam ^ k / (k.factorial : ℝ)
    push_cast
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring

theorem l35_core (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M) :
    ∀ w : ℕ, 1 ≤ w → |delta (stein lam h) w| ≤
      lam⁻¹ * M * (2 + 4 * |(w : ℝ) - lam| * min (1 / Real.sqrt lam) 1) := by
  intro w hw
  have hS := l33_core lam hlam h M hM w hw
  have hE := stein_eq lam hlam h w
  have hP := pe_abs_le lam hlam.le h M hM
  have hM0 := M_nonneg' h M hM
  have hd : delta (stein lam h) w = -lam⁻¹ * (h w - poissonExp lam h - ((w : ℝ) - lam) * stein lam h w) := by
    unfold delta
    field_simp
    linarith
  rw [hd, abs_mul, abs_neg, abs_of_pos (inv_pos.2 hlam)]
  have h2 : |h w - poissonExp lam h| ≤ 2 * M := by
    have := hM w
    calc |h w - poissonExp lam h| ≤ |h w| + |poissonExp lam h| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  have h3 : |((w : ℝ) - lam) * stein lam h w| ≤ |(w : ℝ) - lam| * (4 * M * min (1 / Real.sqrt lam) 1) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hS (abs_nonneg _)
  have h4 := abs_sub (h w - poissonExp lam h) (((w : ℝ) - lam) * stein lam h w)
  calc lam⁻¹ * |h w - poissonExp lam h - ((w : ℝ) - lam) * stein lam h w|
      ≤ lam⁻¹ * (2 * M + |(w : ℝ) - lam| * (4 * M * min (1 / Real.sqrt lam) 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) (inv_pos.2 hlam).le
    _ = lam⁻¹ * M * (2 + 4 * |(w : ℝ) - lam| * min (1 / Real.sqrt lam) 1) := by ring

lemma ae_X_eq_ind {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℕ)
    (hX1 : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ 1) (i : ℕ) :
    (fun ω => (X i ω : ℝ)) =ᵐ[P] {ω | X i ω = 1}.indicator 1 := by
  filter_upwards [hX1 i] with ω hω
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hω with h0 | h1
  · simp [Set.indicator, h0]
  · simp [Set.indicator, h1]

lemma meas_set_eq1 {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℕ) (hXm : ∀ i, Measurable (X i)) (i : ℕ) :
    MeasurableSet {ω | X i ω = 1} := hXm i (measurableSet_singleton 1)

lemma int_X {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℕ) (hXm : ∀ i, Measurable (X i))
    (hX1 : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ 1) (i : ℕ) :
    ∫ ω, (X i ω : ℝ) ∂P = prob P X i := by
  rw [integral_congr_ae (ae_X_eq_ind P X hX1 i), integral_indicator_one (meas_set_eq1 X hXm i)]
  rfl

lemma integ_X {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℕ) (hXm : ∀ i, Measurable (X i))
    (hX1 : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ 1) (i : ℕ) : Integrable (fun ω => (X i ω : ℝ)) P :=
  integ_bdd P _ (mcast _ (hXm i) _) 1 (by filter_upwards [hX1 i] with ω h; exact cast_le_one' _ h)

theorem variance_identity_4_7_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (m : ℕ) :
    Var[fun ω => (W n X ω : ℝ); P] = lam P n X
      + (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
          ∫ ω, (X i ω : ℝ) * X j ω ∂P)
      - (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
          prob P X i * prob P X j)
      + ∑ i ∈ Finset.Icc 1 n, ∫ ω, ((X i ω : ℝ) - prob P X i) * (V n m X i ω : ℝ) ∂P := by
  have hb := basic_identity_core P n X hX m (fun w => (w : ℝ))
  obtain ⟨hXm, _, hX1⟩ := hX
  have hgood : ∀ᵐ ω ∂P, ∀ k, X k ω ≤ 1 := ae_all_iff.mpr hX1
  have hd : ∀ y : ℕ, delta (fun w => (w : ℝ)) y = 1 := by intro y; simp [delta]
  simp only [hd, mul_one] at hb
  have hWm : Measurable (fun ω => (W n X ω : ℝ)) := mcast _ (meas_W n X hXm) _
  have hWb : ∀ᵐ ω ∂P, |(W n X ω : ℝ)| ≤ n := by
    filter_upwards [hgood] with ω hx
    rw [abs_of_nonneg (by positivity)]; exact_mod_cast W_le n X ω hx
  have iW : Integrable (fun ω => (W n X ω : ℝ)) P := integ_bdd P _ hWm n hWb
  have iW2 : Integrable (fun ω => (W n X ω : ℝ) * (W n X ω : ℝ)) P :=
    integ_bdd P _ (hWm.mul hWm) (n * n) (by
      filter_upwards [hWb] with ω h; rw [abs_mul]; exact mul_le_mul h h (abs_nonneg _) (by positivity))
  have hEW : ∫ ω, (W n X ω : ℝ) ∂P = lam P n X := by
    have : (fun ω => (W n X ω : ℝ)) = fun ω => ∑ i ∈ Icc 1 n, (X i ω : ℝ) := by
      funext ω; unfold W; push_cast; rfl
    rw [this, integral_finset_sum _ (fun i _ => integ_X P X hXm hX1 i), lam]
    exact sum_congr rfl (fun i _ => int_X P X hXm hX1 i)
  have hmem : MemLp (fun ω => (W n X ω : ℝ)) 2 P :=
    MemLp.of_bound hWm.aestronglyMeasurable n (by filter_upwards [hWb] with ω h; simpa using h)
  rw [variance_eq_sub hmem]
  have e1 : ∀ ω, (W n X ω : ℝ) * ((W n X ω : ℕ) : ℝ) - lam P n X * (((W n X ω + 1 : ℕ)) : ℝ) =
      (W n X ω : ℝ) * (W n X ω : ℝ) - lam P n X * (W n X ω : ℝ) - lam P n X := by
    intro ω; push_cast; ring
  simp only [e1] at hb
  have hL : ∫ ω, ((W n X ω : ℝ) * (W n X ω : ℝ) - lam P n X * (W n X ω : ℝ) - lam P n X) ∂P =
      ∫ ω, (W n X ω : ℝ) * (W n X ω : ℝ) ∂P - lam P n X * lam P n X - lam P n X := by
    rw [integral_sub ?_ (integrable_const _), integral_sub iW2 (iW.const_mul _),
      integral_const_mul, hEW, integral_const]
    · simp
    · exact iW2.sub (iW.const_mul _)
  rw [hL] at hb
  have e2 : ∀ i, ∫ ω, ((X i ω : ℝ) - prob P X i) * ((V n m X i ω + 1 : ℕ) : ℝ) ∂P =
      ∫ ω, ((X i ω : ℝ) - prob P X i) * (V n m X i ω : ℝ) ∂P := by
    intro i
    have iXp : Integrable (fun ω => (X i ω : ℝ) - prob P X i) P := (integ_X P X hXm hX1 i).sub (integrable_const _)
    have iXV : Integrable (fun ω => ((X i ω : ℝ) - prob P X i) * (V n m X i ω : ℝ)) P := by
      refine integ_bdd P _ (((mcast _ (hXm i) _).sub measurable_const).mul (mcast _ (meas_V n m X hXm i) _))
        ((1 + |prob P X i|) * n) ?_
      filter_upwards [hgood] with ω hx
      rw [abs_mul]
      have a1 := cast_le_one' _ (hx i)
      have : |(X i ω : ℝ) - prob P X i| ≤ 1 + |prob P X i| := (abs_sub _ _).trans (by linarith)
      have hv : |(V n m X i ω : ℝ)| ≤ n := by
        rw [abs_of_nonneg (by positivity)]; exact_mod_cast V_le n m X ω hx i
      gcongr
    have : (fun ω => ((X i ω : ℝ) - prob P X i) * ((V n m X i ω + 1 : ℕ) : ℝ)) =
        fun ω => ((X i ω : ℝ) - prob P X i) * (V n m X i ω : ℝ) + ((X i ω : ℝ) - prob P X i) := by
      funext ω; push_cast; ring
    rw [this, integral_add iXV iXp, integral_sub (integ_X P X hXm hX1 i) (integrable_const _),
      int_X P X hXm hX1 i, integral_const]
    simp
  simp only [e2] at hb
  have e3 : ∀ j : ℕ, ∫ ω, (X j ω : ℝ) ∂P = prob P X j := fun j => int_X P X hXm hX1 j
  simp only [e3] at hb
  have hW2 : (∫ ω, ((fun ω => (W n X ω : ℝ)) ^ 2) ω ∂P) = ∫ ω, (W n X ω : ℝ) * (W n X ω : ℝ) ∂P := by
    congr 1; funext ω; simp [sq]
  rw [hW2, hEW]
  linarith


lemma phi_nonneg {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] {P : Measure Ω}
    {X : ℕ → Ω → β} {φ : ℕ → ℝ} (hφ : IbragimovMixing P X φ) (k : ℕ) : 0 ≤ φ k :=
  Antitone.le_of_tendsto hφ.1 hφ.2.1 k

lemma sigmaIcc_le {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] (X : ℕ → Ω → β)
    (hXm : ∀ i, Measurable (X i)) (a b : ℕ) : sigmaIcc X a b ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le fun i _ => (hXm i).comap_le

lemma sigmaIci_le {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] (X : ℕ → Ω → β)
    (hXm : ∀ i, Measurable (X i)) (a : ℕ) : sigmaIci X a ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le fun i _ => (hXm i).comap_le

lemma cov1 {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → β) (hXm : ∀ i, Measurable (X i)) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ)
    (j k : ℕ) (hk : 1 ≤ k) (A B : Set Ω) (hA : MeasurableSet[sigmaIcc X 1 j] A)
    (hB : MeasurableSet[sigmaIci X (j + k)] B) :
    |P.real (A ∩ B) - P.real A * P.real B| ≤ φ k * P.real A := by
  have hφ0 := phi_nonneg hφ k
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    have hbot : sigmaIcc X 1 0 = ⊥ := by simp [sigmaIcc]
    rw [hbot, MeasurableSpace.measurableSet_bot_iff] at hA
    rcases hA with h | h
    · subst h; simp
    · subst h; simpa using hφ0
  · have hm := sigmaIcc_le X hXm 1 j
    have hBm : MeasurableSet B := sigmaIci_le X hXm (j + k) B hB
    have hAm : MeasurableSet A := hm A hA
    have hmix := hφ.2.2 j k hj hk B hB
    have hint : Integrable (B.indicator (fun _ => (1:ℝ))) P := (integrable_const (1:ℝ)).indicator hBm
    have h1 : P.real (A ∩ B) = ∫ x in A, (P[B.indicator (fun _ => (1 : ℝ)) | sigmaIcc X 1 j]) x ∂P := by
      rw [setIntegral_condExp hm hint hA, setIntegral_indicator hBm, setIntegral_const]
      simp
    have h2 : P.real (A ∩ B) - P.real A * P.real B =
        ∫ x in A, ((P[B.indicator (fun _ => (1 : ℝ)) | sigmaIcc X 1 j]) x - P.real B) ∂P := by
      rw [integral_sub integrable_condExp.integrableOn (integrable_const _), setIntegral_const, ← h1]
      simp
    rw [h2]
    have := norm_setIntegral_le_of_norm_le_const_ae' (μ := P) (s := A) (C := φ k) (measure_lt_top P A)
      (f := fun x => (P[B.indicator (fun _ => (1 : ℝ)) | sigmaIcc X 1 j]) x - P.real B)
      (by filter_upwards [hmix] with ω h _; simpa using h)
    simpa using this

lemma mset_Icc {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℕ) (a b i : ℕ) (hi : a ≤ i ∧ i ≤ b) :
    MeasurableSet[sigmaIcc X a b] {ω | X i ω = 1} := by
  have : MeasurableSpace.comap (X i) inferInstance ≤ sigmaIcc X a b :=
    le_iSup₂ (f := fun i (_ : i ∈ Finset.Icc a b) => MeasurableSpace.comap (X i) inferInstance) i
      (Finset.mem_Icc.mpr hi)
  exact this _ ⟨{1}, measurableSet_singleton 1, rfl⟩

lemma mset_Ici {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℕ) (a i : ℕ) (hi : a ≤ i) :
    MeasurableSet[sigmaIci X a] {ω | X i ω = 1} := by
  have : MeasurableSpace.comap (X i) inferInstance ≤ sigmaIci X a :=
    le_iSup₂ (f := fun i (_ : i ∈ Set.Ici a) => MeasurableSpace.comap (X i) inferInstance) i
      (Set.mem_Ici.mpr hi)
  exact this _ ⟨{1}, measurableSet_singleton 1, rfl⟩

lemma int_XX {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℕ) (hXm : ∀ i, Measurable (X i))
    (hX1 : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ 1) (i k : ℕ) :
    ∫ ω, (X i ω : ℝ) * X k ω ∂P = P.real ({ω | X i ω = 1} ∩ {ω | X k ω = 1}) := by
  have : (fun ω => (X i ω : ℝ) * X k ω) =ᵐ[P] ({ω | X i ω = 1} ∩ {ω | X k ω = 1}).indicator 1 := by
    filter_upwards [ae_X_eq_ind P X hX1 i, ae_X_eq_ind P X hX1 k] with ω h1 h2
    rw [h1, h2]; simp only [Set.indicator, Set.mem_inter_iff, Set.mem_setOf_eq, Pi.one_apply]
    split_ifs <;> simp_all
  rw [integral_congr_ae this, integral_indicator_one ((meas_set_eq1 X hXm i).inter (meas_set_eq1 X hXm k))]

lemma covpair {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℕ) (hXm : ∀ i, Measurable (X i)) (hX1 : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ 1)
    (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ) (m i k : ℕ) (hi : 1 ≤ i) (hk : 1 ≤ k)
    (hik : m < Int.natAbs ((k:ℤ) - i)) :
    |∫ ω, (X i ω : ℝ) * X k ω ∂P - prob P X i * prob P X k| ≤ φ (m + 1) * (prob P X i + prob P X k) := by
  rw [int_XX P X hXm hX1]
  have hp : ∀ j, 0 ≤ prob P X j := fun j => measureReal_nonneg
  have hφ0 := phi_nonneg hφ (m + 1)
  rcases lt_or_gt_of_ne (show i ≠ k by omega) with h | h
  · -- i < k
    have hc := cov1 P X hXm φ hφ i (k - i) (by omega) _ _ (mset_Icc X 1 i i ⟨hi, le_rfl⟩)
      (mset_Ici X (i + (k - i)) k (by omega))
    have hmon : φ (k - i) ≤ φ (m + 1) := hφ.1 (by omega)
    unfold prob
    calc _ ≤ φ (k - i) * P.real {ω | X i ω = 1} := hc
      _ ≤ φ (m + 1) * P.real {ω | X i ω = 1} := mul_le_mul_of_nonneg_right hmon measureReal_nonneg
      _ ≤ _ := by
        have := hp k; unfold prob at this; nlinarith
  · have hc := cov1 P X hXm φ hφ k (i - k) (by omega) _ _ (mset_Icc X 1 k k ⟨hk, le_rfl⟩)
      (mset_Ici X (k + (i - k)) i (by omega))
    have hmon : φ (i - k) ≤ φ (m + 1) := hφ.1 (by omega)
    rw [Set.inter_comm]
    unfold prob
    calc _ = |P.real ({ω | X k ω = 1} ∩ {ω | X i ω = 1}) - P.real {ω | X k ω = 1} * P.real {ω | X i ω = 1}| := by
          rw [mul_comm]
      _ ≤ φ (i - k) * P.real {ω | X k ω = 1} := hc
      _ ≤ φ (m + 1) * P.real {ω | X k ω = 1} := mul_le_mul_of_nonneg_right hmon measureReal_nonneg
      _ ≤ _ := by
        have := hp i; unfold prob at this; nlinarith

lemma int_XpV {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m : ℕ) (X : ℕ → Ω → ℕ) (hXm : ∀ i, Measurable (X i)) (hX1 : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ 1) (i : ℕ) :
    ∫ ω, ((X i ω : ℝ) - prob P X i) * (V n m X i ω : ℝ) ∂P =
      ∑ k ∈ (Icc 1 n).filter (fun k : ℕ => m < Int.natAbs ((k : ℤ) - i)),
        (∫ ω, (X i ω : ℝ) * X k ω ∂P - prob P X i * prob P X k) := by
  have : (fun ω => ((X i ω : ℝ) - prob P X i) * (V n m X i ω : ℝ)) =
      fun ω => ∑ k ∈ (Icc 1 n).filter (fun k : ℕ => m < Int.natAbs ((k : ℤ) - i)),
        ((X i ω : ℝ) * X k ω - prob P X i * X k ω) := by
    funext ω; unfold V; push_cast; rw [mul_sum]; apply sum_congr rfl; intro k _; ring
  rw [this, integral_finset_sum]
  · apply sum_congr rfl; intro k _
    rw [integral_sub, integral_const_mul, int_X P X hXm hX1 k]
    · exact integ_bdd P _ ((mcast _ (hXm i) _).mul (mcast _ (hXm k) _)) 1 (by
        filter_upwards [hX1 i, hX1 k] with ω h1 h2
        rw [abs_mul]; have := cast_le_one' _ h1; have := cast_le_one' _ h2
        calc _ ≤ (1:ℝ) * 1 := by gcongr
          _ = 1 := by ring)
    · exact (integ_X P X hXm hX1 k).const_mul _
  · intro k _
    refine Integrable.sub ?_ ((integ_X P X hXm hX1 k).const_mul _)
    exact integ_bdd P _ ((mcast _ (hXm i) _).mul (mcast _ (hXm k) _)) 1 (by
        filter_upwards [hX1 i, hX1 k] with ω h1 h2
        rw [abs_mul]; have := cast_le_one' _ h1; have := cast_le_one' _ h2
        calc _ ≤ (1:ℝ) * 1 := by gcongr
          _ = 1 := by ring)

theorem bound_4_8_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ)
    (hφ : IbragimovMixing P X φ) (m : ℕ) :
    |∑ i ∈ Finset.Icc 1 n, ∫ ω, ((X i ω : ℝ) - prob P X i) * (V n m X i ω : ℝ) ∂P|
      ≤ 4 * lam P n X * n * φ (m + 1) := by
  obtain ⟨hXm, _, hX1⟩ := hX
  have hp : ∀ j, 0 ≤ prob P X j := fun j => measureReal_nonneg
  have hφ0 := phi_nonneg hφ (m + 1)
  have hl : 0 ≤ lam P n X := sum_nonneg (fun j _ => hp j)
  simp only [int_XpV P n m X hXm hX1]
  have step : ∀ i ∈ Icc 1 n, |∑ k ∈ (Icc 1 n).filter (fun k : ℕ => m < Int.natAbs ((k : ℤ) - i)),
        (∫ ω, (X i ω : ℝ) * X k ω ∂P - prob P X i * prob P X k)| ≤
        ∑ k ∈ Icc 1 n, φ (m + 1) * (prob P X i + prob P X k) := by
    intro i hi
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_sum (fun k hk => ?_)).trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun k _ _ => mul_nonneg hφ0 (add_nonneg (hp i) (hp k))))
    simp only [mem_filter, mem_Icc] at hk hi
    exact covpair P X hXm hX1 φ hφ m i k hi.1 hk.1.1 hk.2
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum step).trans ?_)
  simp only [← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul, Nat.card_Icc, add_tsub_cancel_right]
  have : ∑ i ∈ Icc 1 n, prob P X i = lam P n X := rfl
  rw [this]
  nlinarith [mul_nonneg (mul_nonneg hl (Nat.cast_nonneg n : (0:ℝ) ≤ n)) hφ0]

lemma card_nbhd (n m i : ℕ) :
    ((Icc 1 n).filter (fun j : ℕ => |(i : ℤ) - (j : ℕ)| ≤ m)).card ≤ 2 * m + 1 := by
  have hsub : (Icc 1 n).filter (fun j : ℕ => |(i : ℤ) - (j : ℕ)| ≤ m) ⊆ Icc (i - m) (i + m) := by
    intro j hj; simp only [mem_filter, mem_Icc, abs_le] at hj ⊢; omega
  have := card_le_card hsub
  rw [Nat.card_Icc] at this; omega

lemma pp_bound (p : ℕ → ℝ) (n m : ℕ) :
    ∑ i ∈ Icc 1 n, ∑ j ∈ Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m, p i * p j ≤
      (2 * m + 1) * ∑ i ∈ Icc 1 n, p i ^ 2 := by
  have h1 : ∀ i j : ℕ, p i * p j ≤ (p i ^ 2 + p j ^ 2) / 2 := fun i j => by nlinarith [sq_nonneg (p i - p j)]
  have hA : ∑ i ∈ Icc 1 n, ∑ j ∈ Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m, p j ^ 2 =
      ∑ i ∈ Icc 1 n, ∑ j ∈ Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m, p i ^ 2 := by
    simp only [sum_filter]
    rw [sum_comm]
    apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _
    rw [abs_sub_comm]
  have hB : ∑ i ∈ Icc 1 n, ∑ j ∈ Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m, p i ^ 2 ≤
      (2 * m + 1) * ∑ i ∈ Icc 1 n, p i ^ 2 := by
    rw [mul_sum]; apply sum_le_sum; intro i _
    rw [sum_const, nsmul_eq_mul]
    have hc : ((((Icc 1 n).filter (fun j : ℕ => |(i : ℤ) - (j : ℕ)| ≤ m)).card : ℕ) : ℝ) ≤ 2 * m + 1 := by
      exact_mod_cast card_nbhd n m i
    nlinarith [sq_nonneg (p i)]
  calc _ ≤ ∑ i ∈ Icc 1 n, ∑ j ∈ Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m, (p i ^ 2 + p j ^ 2) / 2 :=
        sum_le_sum (fun i _ => sum_le_sum (fun j _ => h1 i j))
    _ = (∑ i ∈ Icc 1 n, ∑ j ∈ Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m, p i ^ 2 +
          ∑ i ∈ Icc 1 n, ∑ j ∈ Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m, p j ^ 2) / 2 := by
        rw [← sum_add_distrib, sum_div]; apply sum_congr rfl; intro i _
        rw [← sum_add_distrib, sum_div]
    _ ≤ _ := by rw [hA]; linarith

theorem lemma_4_5_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ)
    (hφ : IbragimovMixing P X φ) (m : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
        ∫ ω, (X i ω : ℝ) * X j ω ∂P
      ≤ Var[fun ω => (W n X ω : ℝ); P] - lam P n X + (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2
        + 4 * lam P n X * n * φ (m + 1) := by
  have h1 := variance_identity_4_7_core P n X hX m
  have h2 := bound_4_8_core P n X hX φ hφ m
  have h3 := pp_bound (prob P X) n m
  have h4 := neg_abs_le (∑ i ∈ Finset.Icc 1 n, ∫ ω, ((X i ω : ℝ) - prob P X i) * (V n m X i ω : ℝ) ∂P)
  linarith


theorem var_subset_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ)
    (hφ : IbragimovMixing P X φ) (m : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 n) :
    Var[fun ω => ((∑ k ∈ S, X k ω : ℕ) : ℝ); P] ≤ lam P n X * ((2 * m + 1) + 2 * n * φ (m + 1)) := by
  obtain ⟨hXm, _, hX1⟩ := hX
  have hgood : ∀ᵐ ω ∂P, ∀ k, X k ω ≤ 1 := ae_all_iff.mpr hX1
  have hp : ∀ j, 0 ≤ prob P X j := fun j => measureReal_nonneg
  have hφ0 := phi_nonneg hφ (m + 1)
  have hFeq : (fun ω => ((∑ k ∈ S, X k ω : ℕ) : ℝ)) = fun ω => ∑ k ∈ S, (X k ω : ℝ) := by
    funext ω; push_cast; rfl
  rw [hFeq]
  have hFm : Measurable (fun ω => ∑ k ∈ S, (X k ω : ℝ)) :=
    Finset.measurable_sum _ (fun k _ => mcast _ (hXm k) _)
  have hFb : ∀ᵐ ω ∂P, ‖∑ k ∈ S, (X k ω : ℝ)‖ ≤ n := by
    filter_upwards [hgood] with ω hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := sub_le_n n (fun k => X k ω) hx S hS
    exact_mod_cast this
  have hmem : MemLp (fun ω => ∑ k ∈ S, (X k ω : ℝ)) 2 P :=
    MemLp.of_bound hFm.aestronglyMeasurable n hFb
  rw [variance_eq_sub hmem]
  have iXX : ∀ k l, Integrable (fun ω => (X k ω : ℝ) * X l ω) P := fun k l =>
    integ_bdd P _ ((mcast _ (hXm k) _).mul (mcast _ (hXm l) _)) 1 (by
        filter_upwards [hX1 k, hX1 l] with ω h1 h2
        rw [abs_mul]; have := cast_le_one' _ h1; have := cast_le_one' _ h2
        calc _ ≤ (1:ℝ) * 1 := by gcongr
          _ = 1 := by ring)
  have hE : ∫ ω, ∑ k ∈ S, (X k ω : ℝ) ∂P = ∑ k ∈ S, prob P X k := by
    rw [integral_finset_sum _ (fun i _ => integ_X P X hXm hX1 i)]
    exact sum_congr rfl (fun i _ => int_X P X hXm hX1 i)
  have hE2 : ∫ ω, ((fun ω => ∑ k ∈ S, (X k ω : ℝ)) ^ 2) ω ∂P
      = ∑ k ∈ S, ∑ l ∈ S, ∫ ω, (X k ω : ℝ) * X l ω ∂P := by
    have : ((fun ω => ∑ k ∈ S, (X k ω : ℝ)) ^ 2) = fun ω => ∑ k ∈ S, ∑ l ∈ S, (X k ω : ℝ) * X l ω := by
      funext ω; rw [Pi.pow_apply, sq, sum_mul_sum]
    rw [this, integral_finset_sum _ (fun k _ => integrable_finset_sum _ (fun l _ => iXX k l))]
    exact sum_congr rfl (fun k _ => integral_finset_sum _ (fun l _ => iXX k l))
  rw [hE2, hE, sq, sum_mul_sum, ← sum_sub_distrib]
  simp only [← sum_sub_distrib]
  have hterm : ∀ k ∈ S, ∀ l ∈ S, ∫ ω, (X k ω : ℝ) * X l ω ∂P - prob P X k * prob P X l ≤
      (if |(k:ℤ) - (l:ℕ)| ≤ m then prob P X k else 0) + φ (m+1) * (prob P X k + prob P X l) := by
    intro k hk l hl
    have hk1 := (mem_Icc.mp (hS hk)).1
    have hl1 := (mem_Icc.mp (hS hl)).1
    split_ifs with h
    · have : ∫ ω, (X k ω : ℝ) * X l ω ∂P ≤ prob P X k := by
        rw [int_XX P X hXm hX1]; exact measureReal_mono Set.inter_subset_left
      nlinarith [hp k, hp l, mul_nonneg (hp k) (hp l), mul_nonneg hφ0 (add_nonneg (hp k) (hp l))]
    · have h2 := covpair P X hXm hX1 φ hφ m k l hk1 hl1 (by rw [abs_le] at h; omega)
      have := le_abs_self (∫ ω, (X k ω : ℝ) * X l ω ∂P - prob P X k * prob P X l)
      linarith
  have hsum := sum_le_sum (fun k hk => sum_le_sum (fun l hl => hterm k hk l hl))
  refine hsum.trans ?_
  simp only [sum_add_distrib]
  have hcard : ∀ k ∈ S, ∑ l ∈ S, (if |(k:ℤ) - (l:ℕ)| ≤ m then prob P X k else 0) ≤ (2 * m + 1) * prob P X k := by
    intro k _
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hsub : S.filter (fun l : ℕ => |(k:ℤ) - (l:ℕ)| ≤ m) ⊆ (Icc 1 n).filter (fun j : ℕ => |(k : ℤ) - (j : ℕ)| ≤ m) :=
      filter_subset_filter _ hS
    have hc : ((S.filter (fun l : ℕ => |(k:ℤ) - (l:ℕ)| ≤ m)).card : ℝ) ≤ 2 * m + 1 := by
      have := (card_le_card hsub).trans (card_nbhd n m k)
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right hc (hp k)
  have hA := sum_le_sum hcard
  have hB : ∑ k ∈ S, ∑ l ∈ S, φ (m + 1) * (prob P X k + prob P X l) = φ (m+1) * (2 * S.card * ∑ k ∈ S, prob P X k) := by
    simp only [← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul]
    ring
  rw [hB]
  have hSp : ∑ k ∈ S, prob P X k ≤ lam P n X := sum_le_sum_of_subset_of_nonneg hS (fun j _ _ => hp j)
  have hSc : (S.card : ℝ) ≤ n := by
    have := card_le_card hS; rw [Nat.card_Icc] at this; exact_mod_cast (by omega : S.card ≤ n)
  have hSp0 : 0 ≤ ∑ k ∈ S, prob P X k := sum_nonneg (fun j _ => hp j)
  rw [← mul_sum] at hA
  have hl0 : 0 ≤ lam P n X := hSp0.trans hSp
  have : φ (m+1) * (2 * S.card * ∑ k ∈ S, prob P X k) ≤ φ (m+1) * (2 * n * lam P n X) := by
    apply mul_le_mul_of_nonneg_left _ hφ0
    apply mul_le_mul (by linarith) hSp hSp0 (by positivity)
  nlinarith

lemma sqrt_var_bound (V lam nφ : ℝ) (m : ℕ) (hl : 0 ≤ lam) (hnφ : 0 ≤ nφ)
    (h : V ≤ lam * ((2 * m + 1) + 2 * nφ)) :
    Real.sqrt V ≤ Real.sqrt lam * (m + 1 + 2 * Real.sqrt nφ) := by
  have hs := Real.sq_sqrt hnφ
  have hs0 := Real.sqrt_nonneg nφ
  have hK : 0 ≤ (m:ℝ) + 1 + 2 * Real.sqrt nφ := by positivity
  rw [← Real.sqrt_sq hK, ← Real.sqrt_mul hl]
  apply Real.sqrt_le_sqrt
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hl)
  nlinarith [sq_nonneg (m:ℝ)]

theorem lemma_4_4_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ) (m : ℕ) :
    Real.sqrt (Var[fun ω => (W n X ω : ℝ); P]) ≤
      Real.sqrt (lam P n X) * (m + 1 + 2 * Real.sqrt ((n : ℝ) * φ (m + 1))) := by
  have h := var_subset_le P n X hX φ hφ m (Icc 1 n) (subset_refl _)
  have hl : 0 ≤ lam P n X := sum_nonneg (fun j _ => measureReal_nonneg)
  exact sqrt_var_bound _ _ _ m hl (mul_nonneg (Nat.cast_nonneg n) (phi_nonneg hφ (m+1)))
    (le_of_le_of_eq h (by ring))

theorem bound_4_16_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ) (m : ℕ) (i j : ℕ) :
    ∫ ω, |(Vij n m X i j ω : ℝ) - ∫ ω', (Vij n m X i j ω' : ℝ) ∂P| ∂P
        ≤ Real.sqrt (Var[fun ω => (Vij n m X i j ω : ℝ); P]) ∧
      Real.sqrt (Var[fun ω => (Vij n m X i j ω : ℝ); P])
        ≤ Real.sqrt (lam P n X) * (m + 1 + 2 * Real.sqrt ((n : ℝ) * φ (m + 1))) := by
  constructor
  · obtain ⟨hXm, _, hX1⟩ := hX
    have hgood : ∀ᵐ ω ∂P, ∀ k, X k ω ≤ 1 := ae_all_iff.mpr hX1
    set F : Ω → ℝ := fun ω => (Vij n m X i j ω : ℝ) with hF
    have hFm : Measurable F := by
      apply mcast; unfold Vij; exact Finset.measurable_sum _ (fun k _ => hXm k)
    have hFb : ∀ᵐ ω ∂P, ‖F ω‖ ≤ n := by
      filter_upwards [hgood] with ω hx
      rw [Real.norm_eq_abs, hF, abs_of_nonneg (by positivity)]
      have := sub_le_n n (fun k => X k ω) hx _ (filter_subset (fun k : ℕ =>
        m < Int.natAbs (((k : ℕ) : ℤ) - i) ∧ m < Int.natAbs (((k : ℕ) : ℤ) - j)) (Icc 1 n))
      have h2 : Vij n m X i j ω ≤ n := this
      show (Vij n m X i j ω : ℝ) ≤ n
      exact_mod_cast h2
    have hmem : MemLp F 2 P := MemLp.of_bound hFm.aestronglyMeasurable n hFb
    set c := ∫ ω', F ω' ∂P
    set G : Ω → ℝ := fun ω => |F ω - c| with hG
    have hGm : Measurable G := (hFm.sub measurable_const).abs
    have hGmem : MemLp G 2 P := MemLp.of_bound hGm.aestronglyMeasurable (n + |c|) (by
      filter_upwards [hFb] with ω h
      rw [Real.norm_eq_abs, hG, abs_abs]; rw [Real.norm_eq_abs] at h
      exact (abs_sub _ _).trans (by linarith))
    have hv := variance_nonneg G P
    rw [variance_eq_sub hGmem] at hv
    have hVar : Var[F; P] = ∫ ω, (G ^ 2) ω ∂P := by
      rw [variance_eq_sub hmem]
      have e : ∀ ω, (G ^ 2) ω = (F ω) ^ 2 - 2 * c * F ω + c ^ 2 := by
        intro ω; simp only [Pi.pow_apply, hG, sq_abs]; ring
      simp only [e]
      have iF : Integrable F P := hmem.integrable one_le_two
      have iF2 : Integrable (fun ω => F ω ^ 2) P := hmem.integrable_sq
      rw [integral_add (f := fun ω => F ω ^ 2 - 2 * c * F ω) (g := fun _ => c ^ 2)
        (iF2.sub (iF.const_mul _)) (integrable_const _)]
      rw [integral_sub (f := fun ω => F ω ^ 2) (g := fun ω => 2 * c * F ω) iF2 (iF.const_mul _),
        integral_const_mul, integral_const]
      simp only [Pi.pow_apply, probReal_univ, smul_eq_mul, one_mul]
      ring
    change ∫ ω, G ω ∂P ≤ Real.sqrt (Var[F; P])
    rw [hVar]
    have h0 : 0 ≤ ∫ ω, G ω ∂P := integral_nonneg (fun ω => abs_nonneg _)
    rw [← Real.sqrt_sq h0]
    exact Real.sqrt_le_sqrt (by linarith)
  · have h := var_subset_le P n X hX φ hφ m _ (filter_subset (fun k : ℕ =>
      m < Int.natAbs (((k : ℕ) : ℤ) - i) ∧ m < Int.natAbs (((k : ℕ) : ℤ) - j)) (Icc 1 n))
    have hl : 0 ≤ lam P n X := sum_nonneg (fun j _ => measureReal_nonneg)
    exact sqrt_var_bound _ _ _ m hl (mul_nonneg (Nat.cast_nonneg n) (phi_nonneg hφ (m+1)))
      (le_of_le_of_eq h (by ring))


lemma X_meas_Icc {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℕ) (a b k : ℕ) (hk : a ≤ k ∧ k ≤ b) :
    Measurable[sigmaIcc X a b] (X k) := by
  have : MeasurableSpace.comap (X k) inferInstance ≤ sigmaIcc X a b :=
    le_iSup₂ (f := fun i (_ : i ∈ Finset.Icc a b) => MeasurableSpace.comap (X i) inferInstance) k
      (Finset.mem_Icc.mpr hk)
  intro s hs; exact this _ ⟨s, hs, rfl⟩

lemma X_meas_Ici {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℕ) (a k : ℕ) (hk : a ≤ k) :
    Measurable[sigmaIci X a] (X k) := by
  have : MeasurableSpace.comap (X k) inferInstance ≤ sigmaIci X a :=
    le_iSup₂ (f := fun i (_ : i ∈ Set.Ici a) => MeasurableSpace.comap (X i) inferInstance) k
      (Set.mem_Ici.mpr hk)
  intro s hs; exact this _ ⟨s, hs, rfl⟩

lemma integral_mul_ind_condExp {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G ≤ mΩ) (U : Ω → ℝ) (hU : Measurable[G] U) (C : ℝ)
    (hUb : ∀ᵐ ω ∂P, |U ω| ≤ C) (B : Set Ω) (hB : MeasurableSet[mΩ] B) :
    ∫ ω, U ω * B.indicator (fun _ => (1:ℝ)) ω ∂P
      = ∫ ω, U ω * (P[B.indicator (fun _ => (1:ℝ)) | G]) ω ∂P := by
  have hUs : StronglyMeasurable[G] U := hU.stronglyMeasurable
  have hint : Integrable (B.indicator (fun _ => (1:ℝ))) P := (integrable_const (1:ℝ)).indicator hB
  have h1 := condExp_stronglyMeasurable_mul_of_bound hG hUs hint C
    (by filter_upwards [hUb] with ω h; simpa using h)
  have h2 : ∫ ω, U ω * B.indicator (fun _ => (1:ℝ)) ω ∂P = ∫ ω, (U * B.indicator (fun _ => (1:ℝ))) ω ∂P := rfl
  rw [h2, ← integral_condExp hG]
  exact integral_congr_ae h1

lemma mix_U {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℕ) (hXm : ∀ i, Measurable (X i)) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ)
    (j k : ℕ) (hk : 1 ≤ k) (U : Ω → ℝ) (hU : Measurable[sigmaIcc X 1 j] U) (C : ℝ)
    (hUb : ∀ᵐ ω ∂P, |U ω| ≤ C)
    (B : Set Ω) (hB : MeasurableSet[sigmaIci X (j + k)] B) :
    |∫ ω, U ω * B.indicator (fun _ => (1:ℝ)) ω ∂P - (∫ ω, U ω ∂P) * P.real B|
      ≤ φ k * ∫ ω, |U ω| ∂P := by
  have hφ0 := phi_nonneg hφ k
  have hGle := sigmaIcc_le X hXm 1 j
  have hBm : MeasurableSet B := sigmaIci_le X hXm (j + k) B hB
  have hUm : Measurable U := hU.mono hGle le_rfl
  have iU : Integrable U P := integ_bdd P U hUm C hUb
  have hI0 : 0 ≤ φ k * ∫ ω, |U ω| ∂P := mul_nonneg hφ0 (integral_nonneg (fun _ => abs_nonneg _))
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    have hbot : sigmaIcc X 1 0 = ⊥ := by simp [sigmaIcc]
    rw [hbot] at hU
    obtain ⟨ω0, -⟩ : (Set.univ : Set Ω).Nonempty := nonempty_of_measure_ne_zero (μ := P) (by simp)
    have hc : ∀ ω, U ω = U ω0 := by
      intro ω
      have := hU (measurableSet_singleton (U ω0))
      rcases MeasurableSpace.measurableSet_bot_iff.mp this with h | h
      · have : ω0 ∈ U ⁻¹' {U ω0} := rfl
        rw [h] at this; exact absurd this (Set.notMem_empty _)
      · have : ω ∈ U ⁻¹' {U ω0} := by rw [h]; trivial
        exact this
    have e1 : (fun ω => U ω * B.indicator (fun _ => (1:ℝ)) ω) = fun ω => U ω0 * B.indicator (fun _ => (1:ℝ)) ω := by
      funext ω; rw [hc ω]
    have e2 : (fun ω => U ω) = fun _ => U ω0 := funext hc
    rw [e1, e2, integral_const_mul, integral_indicator hBm, setIntegral_const, integral_const]
    simp [hI0]
  · have hmix := hφ.2.2 j k hj hk B hB
    rw [integral_mul_ind_condExp P _ hGle U hU C hUb B hBm]
    set c := P[B.indicator (fun _ => (1:ℝ)) | sigmaIcc X 1 j]
    have ic : Integrable c P := integrable_condExp
    have iUc : Integrable (fun ω => U ω * c ω) P := ic.bdd_mul hUm.aestronglyMeasurable
      (by filter_upwards [hUb] with ω h; simpa using h)
    have e : ∫ ω, U ω * c ω ∂P - (∫ ω, U ω ∂P) * P.real B = ∫ ω, U ω * (c ω - P.real B) ∂P := by
      rw [← integral_mul_const, ← integral_sub iUc (iU.mul_const _)]
      congr 1; funext ω; ring
    rw [e]
    refine (abs_integral_le_integral_abs).trans ?_
    rw [← integral_const_mul]
    apply integral_mono_ae
    · exact ((ic.sub (integrable_const (P.real B))).bdd_mul hUm.aestronglyMeasurable
        (by filter_upwards [hUb] with ω h; simpa using h)).abs
    · exact iU.abs.const_mul _
    · filter_upwards [hmix] with ω h
      rw [abs_mul, mul_comm (φ k)]
      exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

lemma tv_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℕ) (hXm : ∀ i, Measurable (X i)) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ)
    (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) (Z : Ω → ℕ) (hZ : Measurable[sigmaIci X (j + k)] Z)
    (N : ℕ) (hZN : ∀ᵐ ω ∂P, Z ω < N) :
    ∀ᵐ ω ∂P, ∑ z ∈ range N, |(P[{ω | Z ω = z}.indicator (fun _ => (1:ℝ)) | sigmaIcc X 1 j]) ω
        - P.real {ω | Z ω = z}| ≤ 2 * φ k := by
  have hZm : Measurable Z := hZ.mono (sigmaIci_le X hXm _) le_rfl
  have hmT : ∀ T : Finset ℕ, MeasurableSet[sigmaIci X (j + k)] {ω | Z ω ∈ T} :=
    fun T => hZ T.finite_toSet.measurableSet
  have h1 : ∀ᵐ ω ∂P, ∀ T : Finset ℕ,
      |(P[{ω | Z ω ∈ T}.indicator (fun _ => (1:ℝ)) | sigmaIcc X 1 j]) ω - P.real {ω | Z ω ∈ T}| ≤ φ k :=
    ae_all_iff.mpr (fun T => hφ.2.2 j k hj hk _ (hmT T))
  have hind : ∀ T : Finset ℕ, {ω | Z ω ∈ T}.indicator (fun _ => (1:ℝ))
      = ∑ z ∈ T, {ω | Z ω = z}.indicator (fun _ => (1:ℝ)) := by
    intro T; funext ω
    simp only [Finset.sum_apply, Set.indicator, Set.mem_setOf_eq]
    rw [Finset.sum_ite_eq]
  have hmeas1 : ∀ z, MeasurableSet {ω | Z ω = z} := fun z => hZm (measurableSet_singleton z)
  have hint1 : ∀ z, Integrable ({ω | Z ω = z}.indicator (fun _ => (1:ℝ))) P :=
    fun z => (integrable_const _).indicator (hmeas1 z)
  have h2 : ∀ᵐ ω ∂P, ∀ T : Finset ℕ, (P[{ω | Z ω ∈ T}.indicator (fun _ => (1:ℝ)) | sigmaIcc X 1 j]) ω
      = ∑ z ∈ T, (P[{ω | Z ω = z}.indicator (fun _ => (1:ℝ)) | sigmaIcc X 1 j]) ω := by
    refine ae_all_iff.mpr (fun T => ?_)
    rw [hind T]
    filter_upwards [condExp_finsetSum (fun z _ => hint1 z) (sigmaIcc X 1 j)] with ω h
    rw [h, Finset.sum_apply]
  have hreal : ∀ T : Finset ℕ, P.real {ω | Z ω ∈ T} = ∑ z ∈ T, P.real {ω | Z ω = z} := by
    intro T
    have hU : {ω | Z ω ∈ T} = ⋃ z ∈ T, {ω | Z ω = z} := by ext ω; simp
    rw [hU, measureReal_biUnion_finset]
    · intro a _ b _ hab
      exact Set.disjoint_left.mpr (fun ω h1 h2 => hab (h1.symm.trans h2))
    · intro z _; exact hmeas1 z
  have h3 : P[{ω | Z ω ∈ range N}.indicator (fun _ => (1:ℝ)) | sigmaIcc X 1 j] =ᵐ[P] fun _ => 1 := by
    have : {ω | Z ω ∈ range N}.indicator (fun _ => (1:ℝ)) =ᵐ[P] fun _ => 1 := by
      filter_upwards [hZN] with ω h; simp [Set.indicator, h]
    refine (condExp_congr_ae this).trans ?_
    rw [condExp_const (sigmaIcc_le X hXm 1 j)]
  have hPN : P.real {ω | Z ω ∈ range N} = 1 := by
    have : {ω | Z ω ∈ range N} =ᵐ[P] (Set.univ : Set Ω) := by
      filter_upwards [hZN] with ω h; apply propext; exact ⟨fun _ => trivial, fun _ => show Z ω ∈ range N from mem_range.mpr h⟩
    rw [measureReal_def, measure_congr this]; simp
  filter_upwards [h1, h2, h3] with ω h1 h2 h3
  set d : ℕ → ℝ := fun z => (P[{ω | Z ω = z}.indicator (fun _ => (1:ℝ)) | sigmaIcc X 1 j]) ω
    - P.real {ω | Z ω = z} with hd
  have hsum0 : ∑ z ∈ range N, d z = 0 := by
    simp only [hd, sum_sub_distrib, ← h2 (range N), ← hreal (range N), h3, hPN]; ring
  set T := (range N).filter (fun z => 0 ≤ d z) with hTdef
  have hT : ∑ z ∈ T, d z ≤ φ k := by
    have := h1 T
    simp only [hd, sum_sub_distrib, ← h2 T, ← hreal T]
    exact (le_abs_self _).trans this
  have e1 : ∑ z ∈ range N, |d z| = ∑ z ∈ T, d z + ∑ z ∈ (range N).filter (fun z => ¬ 0 ≤ d z), (-d z) := by
    rw [← sum_filter_add_sum_filter_not (range N) (fun z => 0 ≤ d z)]
    congr 1
    · apply sum_congr rfl; intro z hz; rw [abs_of_nonneg (mem_filter.mp hz).2]
    · apply sum_congr rfl; intro z hz; rw [abs_of_neg (lt_of_not_ge (mem_filter.mp hz).2)]
  have e2 : ∑ z ∈ range N, d z = ∑ z ∈ T, d z + ∑ z ∈ (range N).filter (fun z => ¬ 0 ≤ d z), d z :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  change ∑ z ∈ range N, |d z| ≤ 2 * φ k
  rw [e1, sum_neg_distrib]; linarith

lemma dec2 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℕ) (hXm : ∀ i, Measurable (X i)) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ)
    (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) (U : Ω → ℝ) (hU : Measurable[sigmaIcc X 1 j] U) (C : ℝ)
    (hUb : ∀ᵐ ω ∂P, |U ω| ≤ C) (L : Ω → ℕ) (hL : Measurable[sigmaIcc X 1 j] L)
    (Z : Ω → ℕ) (hZ : Measurable[sigmaIci X (j + k)] Z) (N : ℕ) (hZN : ∀ᵐ ω ∂P, Z ω < N)
    (f : ℕ → ℕ → ℝ) (M : ℝ) (hM : ∀ a b, |f a b| ≤ M) :
    |∫ ω, U ω * f (L ω) (Z ω) ∂P
        - ∫ ω, U ω * (∑ z ∈ range N, f (L ω) z * P.real {ω | Z ω = z}) ∂P|
      ≤ 2 * M * φ k * ∫ ω, |U ω| ∂P := by
  have hGle := sigmaIcc_le X hXm 1 j
  have hUm : Measurable U := hU.mono hGle le_rfl
  have hZm : Measurable Z := hZ.mono (sigmaIci_le X hXm _) le_rfl
  have iU : Integrable U P := integ_bdd P U hUm C hUb
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0)
  have hφ0 := phi_nonneg hφ k
  have hmeas1 : ∀ z, MeasurableSet {ω | Z ω = z} := fun z => hZm (measurableSet_singleton z)
  have hexp : ∀ᵐ ω ∂P, f (L ω) (Z ω) = ∑ z ∈ range N, f (L ω) z * {ω | Z ω = z}.indicator (fun _ => (1:ℝ)) ω := by
    filter_upwards [hZN] with ω hω
    rw [sum_eq_single (Z ω)]
    · simp [Set.indicator]
    · intro b _ hb; simp [Set.indicator, Ne.symm hb]
    · intro h; exact absurd (mem_range.mpr hω) h
  have hV : ∀ z, Measurable[sigmaIcc X 1 j] (fun ω => U ω * f (L ω) z) := fun z =>
    hU.mul ((measurable_from_top (f := fun a => f a z)).comp hL)
  have hVb : ∀ z, ∀ᵐ ω ∂P, |U ω * f (L ω) z| ≤ C * M := by
    intro z; filter_upwards [hUb] with ω h
    rw [abs_mul]; exact mul_le_mul h (hM _ _) (abs_nonneg _) ((abs_nonneg _).trans h)
  have hstep : ∀ z, ∫ ω, U ω * f (L ω) z * {ω | Z ω = z}.indicator (fun _ => (1:ℝ)) ω ∂P
      = ∫ ω, U ω * f (L ω) z * (P[{ω | Z ω = z}.indicator (fun _ => (1:ℝ)) | sigmaIcc X 1 j]) ω ∂P :=
    fun z => integral_mul_ind_condExp P _ hGle _ (hV z) (C * M) (hVb z) _ (hmeas1 z)
  have iVc : ∀ z, Integrable (fun ω => U ω * f (L ω) z *
      (P[{ω | Z ω = z}.indicator (fun _ => (1:ℝ)) | sigmaIcc X 1 j]) ω) P := fun z =>
    integrable_condExp.bdd_mul ((hV z).mono hGle le_rfl).aestronglyMeasurable
      (by filter_upwards [hVb z] with ω h; simpa using h)
  have iVi : ∀ z, Integrable (fun ω => U ω * f (L ω) z * {ω | Z ω = z}.indicator (fun _ => (1:ℝ)) ω) P :=
    fun z => ((integrable_const (1:ℝ)).indicator (hmeas1 z)).bdd_mul
      ((hV z).mono hGle le_rfl).aestronglyMeasurable (by filter_upwards [hVb z] with ω h; simpa using h)
  have iVp : ∀ z, Integrable (fun ω => U ω * f (L ω) z * P.real {ω | Z ω = z}) P := fun z =>
    (integ_bdd P _ ((hV z).mono hGle le_rfl) _ (hVb z)).mul_const _
  have eL : ∫ ω, U ω * f (L ω) (Z ω) ∂P = ∑ z ∈ range N, ∫ ω, U ω * f (L ω) z *
      (P[{ω | Z ω = z}.indicator (fun _ => (1:ℝ)) | sigmaIcc X 1 j]) ω ∂P := by
    rw [← sum_congr rfl (fun z _ => hstep z), ← integral_finset_sum _ (fun z _ => iVi z)]
    apply integral_congr_ae; filter_upwards [hexp] with ω hω
    rw [hω, mul_sum]; apply sum_congr rfl; intro z _; ring
  have eR : ∫ ω, U ω * (∑ z ∈ range N, f (L ω) z * P.real {ω | Z ω = z}) ∂P
      = ∑ z ∈ range N, ∫ ω, U ω * f (L ω) z * P.real {ω | Z ω = z} ∂P := by
    rw [← integral_finset_sum _ (fun z _ => iVp z)]
    congr 1; funext ω; rw [mul_sum]; apply sum_congr rfl; intro z _; ring
  rw [eL, eR, ← sum_sub_distrib]
  rw [← sum_congr rfl (fun z _ => integral_sub (iVc z) (iVp z))]
  have iD : ∀ z, Integrable (fun ω => U ω * f (L ω) z *
      (P[{ω | Z ω = z}.indicator (fun _ => (1:ℝ)) | sigmaIcc X 1 j]) ω
      - U ω * f (L ω) z * P.real {ω | Z ω = z}) P := fun z => (iVc z).sub (iVp z)
  rw [← integral_finset_sum _ (fun z _ => iD z)]
  refine (abs_integral_le_integral_abs).trans ?_
  rw [← integral_const_mul]
  apply integral_mono_ae
  · exact (integrable_finset_sum _ (fun z _ => iD z)).abs
  · exact iU.abs.const_mul _
  · filter_upwards [tv_bound P X hXm φ hφ j k hj hk Z hZ N hZN] with ω htv
    have e : ∑ z ∈ range N, (U ω * f (L ω) z *
        (P[{ω | Z ω = z}.indicator (fun _ => (1:ℝ)) | sigmaIcc X 1 j]) ω
        - U ω * f (L ω) z * P.real {ω | Z ω = z}) = U ω * ∑ z ∈ range N, f (L ω) z *
        ((P[{ω | Z ω = z}.indicator (fun _ => (1:ℝ)) | sigmaIcc X 1 j]) ω - P.real {ω | Z ω = z}) := by
      rw [mul_sum]; apply sum_congr rfl; intro z _; ring
    rw [e, abs_mul]
    have hs : |∑ z ∈ range N, f (L ω) z *
        ((P[{ω | Z ω = z}.indicator (fun _ => (1:ℝ)) | sigmaIcc X 1 j]) ω - P.real {ω | Z ω = z})|
        ≤ M * (2 * φ k) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      refine le_trans (sum_le_sum (g := fun z => M * |(P[{ω | Z ω = z}.indicator (fun _ => (1:ℝ)) |
          sigmaIcc X 1 j]) ω - P.real {ω | Z ω = z}|) (fun z _ => ?_)) ?_
      · rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hM _ _) (abs_nonneg _)
      · rw [← mul_sum]; exact mul_le_mul_of_nonneg_left htv hM0
    calc |U ω| * _ ≤ |U ω| * (M * (2 * φ k)) := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
      _ = 2 * M * φ k * |U ω| := by ring


lemma sum_meas_Icc {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℕ) (T : Finset ℕ) (j : ℕ)
    (hT : ∀ k ∈ T, 1 ≤ k ∧ k ≤ j) : Measurable[sigmaIcc X 1 j] (fun ω => ∑ k ∈ T, X k ω) :=
  Finset.measurable_sum T (fun k hk => X_meas_Icc X 1 j k (hT k hk))

lemma sum_meas_Ici {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℕ) (T : Finset ℕ) (a : ℕ)
    (hT : ∀ k ∈ T, a ≤ k) : Measurable[sigmaIci X a] (fun ω => ∑ k ∈ T, X k ω) :=
  Finset.measurable_sum T (fun k hk => X_meas_Ici X a k (hT k hk))

lemma V_split' (n m i : ℕ) (x : ℕ → ℕ) :
    ∑ k ∈ Icc 1 n with m < Int.natAbs (((k : ℕ) : ℤ) - i), x k =
      ∑ k ∈ Icc 1 n with k + m < i, x k + ∑ k ∈ Icc 1 n with i + m < k, x k := by
  simp only [sum_filter, ← sum_add_distrib]
  apply sum_congr rfl; intro k _
  split_ifs <;> omega

lemma sum_preal_le_one {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℕ) (hZ : Measurable Z) (T : Finset ℕ) : ∑ z ∈ T, P.real {ω | Z ω = z} ≤ 1 := by
  rw [← measureReal_biUnion_finset]
  · exact measureReal_le_one
  · intro a _ b _ hab
    exact Set.disjoint_left.mpr (fun ω h1 h2 => hab (h1.symm.trans h2))
  · intro z _; exact hZ (measurableSet_singleton z)

lemma gbar_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℕ) (hZ : Measurable Z) (N : ℕ) (g : ℕ → ℝ) (M : ℝ) (hg : ∀ z, |g z| ≤ M) :
    |∑ z ∈ range N, g z * P.real {ω | Z ω = z}| ≤ M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hg 0)
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ z ∈ range N, |g z * P.real {ω | Z ω = z}| ≤ ∑ z ∈ range N, M * P.real {ω | Z ω = z} := by
        apply sum_le_sum; intro z _
        rw [abs_mul, abs_of_nonneg measureReal_nonneg]
        exact mul_le_mul_of_nonneg_right (hg z) measureReal_nonneg
    _ = M * ∑ z ∈ range N, P.real {ω | Z ω = z} := by rw [mul_sum]
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left (sum_preal_le_one P Z hZ _) hM0
    _ = M := mul_one M

lemma l46_term {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ)
    (m : ℕ) (f : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |f k| ≤ M) (i : ℕ) (hi : i ∈ Icc 1 n) :
    |∫ ω, ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1) ∂P| ≤ 3 * M * φ (m + 1) := by
  obtain ⟨hXm, _, hX1⟩ := hX
  have hgood : ∀ᵐ ω ∂P, ∀ k, X k ω ≤ 1 := ae_all_iff.mpr hX1
  have hi1 : 1 ≤ i := (mem_Icc.mp hi).1
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hφ0 := phi_nonneg hφ (m + 1)
  have hp0 : 0 ≤ prob P X i := measureReal_nonneg
  have hp1 : prob P X i ≤ 1 := measureReal_le_one
  have hV : ∀ ω, V n m X i ω = (fun ω => ∑ k ∈ Icc 1 n with k + m < i, X k ω) ω
      + (fun ω => ∑ k ∈ Icc 1 n with i + m < k, X k ω) ω := fun ω => V_split' n m i (fun k => X k ω)
  set Lf : Ω → ℕ := fun ω => ∑ k ∈ Icc 1 n with k + m < i, X k ω with hLf
  set Rf : Ω → ℕ := fun ω => ∑ k ∈ Icc 1 n with i + m < k, X k ω with hRf
  set U : Ω → ℝ := fun ω => (X i ω : ℝ) - prob P X i with hU
  have hUm : Measurable[sigmaIcc X 1 i] U :=
    ((measurable_from_top (f := fun k : ℕ => (k : ℝ))).comp (X_meas_Icc X 1 i i ⟨hi1, le_rfl⟩)).sub
      measurable_const
  have hUb : ∀ᵐ ω ∂P, |U ω| ≤ 1 := by
    filter_upwards [hX1 i] with ω h
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
    · simp only [hU, h0]; rw [abs_le]; constructor <;> push_cast <;> linarith
    · simp only [hU, h1]; rw [abs_le]; constructor <;> push_cast <;> linarith
  have hUint : ∫ ω, |U ω| ∂P ≤ 1 := by
    calc ∫ ω, |U ω| ∂P ≤ ∫ _ω, (1:ℝ) ∂P := integral_mono_ae
          (integ_bdd P _ ((hUm.mono (sigmaIcc_le X hXm 1 i) le_rfl).abs) 1
            (by filter_upwards [hUb] with ω h; rwa [abs_abs])) (integrable_const _) hUb
      _ = 1 := by simp
  have hRN : ∀ᵐ ω ∂P, Rf ω < n + 1 := by
    filter_upwards [hgood] with ω hx
    have := sub_le_n n (fun k => X k ω) hx _ (filter_subset (fun k : ℕ => i + m < k) (Icc 1 n))
    simp only [hRf]; omega
  have hLmeas : Measurable[sigmaIcc X 1 i] Lf := sum_meas_Icc X _ i (by
    intro k hk; simp only [mem_filter, mem_Icc] at hk; omega)
  have hRmeas : Measurable[sigmaIci X (i + (m + 1))] Rf := sum_meas_Ici X _ _ (by
    intro k hk; simp only [mem_filter, mem_Icc] at hk; omega)
  have hRm : Measurable Rf := hRmeas.mono (sigmaIci_le X hXm _) le_rfl
  have d := dec2 P X hXm φ hφ i (m + 1) hi1 (by omega) U hUm 1 hUb Lf hLmeas Rf hRmeas (n + 1) hRN
    (fun a b => f (a + b + 1)) M (fun a b => hM _)
  have e1 : ∫ ω, ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1) ∂P
      = ∫ ω, U ω * (fun a b => f (a + b + 1)) (Lf ω) (Rf ω) ∂P := by
    congr 1; funext ω; simp only [hU]; rw [hV ω]
  set gb : ℕ → ℝ := fun l => ∑ z ∈ range (n + 1), (fun a b => f (a + b + 1)) l z * P.real {ω | Rf ω = z}
    with hgb
  have hgbM : ∀ l, |gb l| ≤ M := fun l => gbar_le P Rf hRm (n + 1) _ M (fun z => hM _)
  have step2 : |∫ ω, U ω * gb (Lf ω) ∂P| ≤ M * φ (m + 1) := by
    rcases le_or_gt i m with him | him
    · have hL0 : ∀ ω, Lf ω = 0 := by
        intro ω; simp only [hLf]; apply sum_eq_zero; intro k hk
        simp only [mem_filter, mem_Icc] at hk; omega
      have : ∫ ω, U ω * gb (Lf ω) ∂P = 0 := by
        simp only [hL0, hU]
        rw [integral_mul_const, integral_sub (integ_X P X hXm hX1 i) (integrable_const _),
          int_X P X hXm hX1 i, integral_const]
        simp
      rw [this, abs_zero]; exact mul_nonneg hM0 hφ0
    · have hLmeas' : Measurable[sigmaIcc X 1 (i - (m + 1))] Lf := sum_meas_Icc X _ _ (by
        intro k hk; simp only [mem_filter, mem_Icc] at hk; omega)
      have hGm : Measurable[sigmaIcc X 1 (i - (m + 1))] (fun ω => gb (Lf ω)) :=
        (measurable_from_top (f := gb)).comp hLmeas'
      have hB : MeasurableSet[sigmaIci X (i - (m + 1) + (m + 1))] {ω | X i ω = 1} :=
        mset_Ici X _ i (by omega)
      have mx := mix_U P X hXm φ hφ (i - (m + 1)) (m + 1) (by omega) (fun ω => gb (Lf ω)) hGm M
        (Filter.Eventually.of_forall (fun ω => hgbM _)) _ hB
      have hGm' : Measurable (fun ω => gb (Lf ω)) := hGm.mono (sigmaIcc_le X hXm 1 _) le_rfl
      have iG : Integrable (fun ω => gb (Lf ω)) P :=
        integ_bdd P _ hGm' M (Filter.Eventually.of_forall (fun ω => hgbM _))
      have e : ∫ ω, U ω * gb (Lf ω) ∂P = ∫ ω, gb (Lf ω) * {ω | X i ω = 1}.indicator (fun _ => (1:ℝ)) ω ∂P
          - (∫ ω, gb (Lf ω) ∂P) * prob P X i := by
        rw [← integral_mul_const, ← integral_sub]
        · apply integral_congr_ae
          filter_upwards [hX1 i] with ω h
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
          · simp [hU, h0, Set.indicator]; ring
          · simp [hU, h1, Set.indicator]; ring
        · exact ((integrable_const (1:ℝ)).indicator (meas_set_eq1 X hXm i)).bdd_mul
            hGm'.aestronglyMeasurable (Filter.Eventually.of_forall (fun ω => by simpa using hgbM _))
        · exact iG.mul_const _
      rw [e]
      refine mx.trans ?_
      have : ∫ ω, |gb (Lf ω)| ∂P ≤ M := by
        calc ∫ ω, |gb (Lf ω)| ∂P ≤ ∫ _ω, M ∂P := integral_mono_ae iG.abs (integrable_const _)
              (Filter.Eventually.of_forall (fun ω => hgbM _))
          _ = M := by simp
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right this hφ0
  rw [e1]
  have d' : |∫ ω, U ω * (fun a b => f (a + b + 1)) (Lf ω) (Rf ω) ∂P - ∫ ω, U ω * gb (Lf ω) ∂P|
      ≤ 2 * M * φ (m + 1) * ∫ ω, |U ω| ∂P := d
  have h3 : 2 * M * φ (m + 1) * ∫ ω, |U ω| ∂P ≤ 2 * M * φ (m + 1) :=
    mul_le_of_le_one_right (by positivity) hUint
  have := abs_sub_abs_le_abs_sub (∫ ω, U ω * (fun a b => f (a + b + 1)) (Lf ω) (Rf ω) ∂P)
    (∫ ω, U ω * gb (Lf ω) ∂P)
  linarith

theorem lemma_4_6_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ) (m : ℕ)
    (f : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |f k| ≤ M) :
    |∑ i ∈ Finset.Icc 1 n, ∫ ω, ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1) ∂P|
      ≤ 6 * M * n * φ (m + 1) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hφ0 := phi_nonneg hφ (m + 1)
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine (sum_le_sum (fun i hi => l46_term P n X hX φ hφ m f M hM i hi)).trans ?_
  rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
  simp only [add_tsub_cancel_right]
  nlinarith [mul_nonneg (mul_nonneg hM0 hφ0) (Nat.cast_nonneg n : (0:ℝ) ≤ n)]


lemma abs_int_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {F G : Ω → ℝ} (hG : Integrable G P)
    (h : ∀ᵐ ω ∂P, |F ω| ≤ G ω) : |∫ ω, F ω ∂P| ≤ ∫ ω, G ω ∂P :=
  (abs_integral_le_integral_abs).trans
    (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) hG h)

lemma integ_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → ℝ) (hA : Measurable A) (hAb : ∀ᵐ ω ∂P, |A ω| ≤ 1) (Yv : Ω → ℕ) (hY : Measurable Yv)
    (K : ℝ) (hYb : ∀ᵐ ω ∂P, (Yv ω : ℝ) ≤ K) (c μ l : ℝ) :
    Integrable (fun ω => c * (A ω * (1 + 2 * μ * |(Yv ω : ℝ) + 1 - l|))) P := by
  have hYm : Measurable (fun ω => (Yv ω : ℝ)) := mcast _ hY _
  have iY : Integrable (fun ω => (Yv ω : ℝ)) P := integ_bdd P _ hYm K (by
    filter_upwards [hYb] with ω h; rw [abs_of_nonneg (by positivity)]; exact h)
  have iB : Integrable (fun ω => 1 + 2 * μ * |(Yv ω : ℝ) + 1 - l|) P :=
    (integrable_const _).add (((iY.add (integrable_const _)).sub (integrable_const _)).abs.const_mul _)
  have iAB : Integrable (fun ω => A ω * (1 + 2 * μ * |(Yv ω : ℝ) + 1 - l|)) P :=
    iB.bdd_mul hA.aestronglyMeasurable (by filter_upwards [hAb] with ω h; simpa using h)
  exact iAB.const_mul c

lemma pt_bound (lam μ a D w : ℝ) (ha : 0 ≤ a)
    (hD : |D| ≤ lam⁻¹ * 1 * (2 + 4 * |w - lam| * μ)) :
    |a * D| ≤ 2 * lam⁻¹ * (a * (1 + 2 * μ * |w - lam|)) := by
  rw [abs_mul, abs_of_nonneg ha]
  calc a * |D| ≤ a * (lam⁻¹ * 1 * (2 + 4 * |w - lam| * μ)) := mul_le_mul_of_nonneg_left hD ha
    _ = _ := by ring

theorem bound_4_14_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (hlam : 0 < lam P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ) (m : ℕ)
    (h : ℕ → ℝ) (hh : ∀ k, |h k| ≤ 1) :
    |∫ ω, h (W n X ω) ∂P - poissonExp (lam P n X) h| ≤
      2 * (lam P n X)⁻¹ * (∑ i ∈ Finset.Icc 1 n,
          ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - ((j : ℕ) : ℤ)| ∧ |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
            ∫ ω, (X i ω : ℝ) * X j ω *
              (1 + 2 * min (1 / Real.sqrt (lam P n X)) 1 * |(Y' n m X i ((j : ℤ) - 1) ω : ℝ) + 1 - lam P n X|) ∂P)
      + 2 * (lam P n X)⁻¹ * (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
            prob P X i * ∫ ω, (X j ω : ℝ) *
              (1 + 2 * min (1 / Real.sqrt (lam P n X)) 1 * |(Y n m X i ((j : ℤ) - 1) ω : ℝ) + 1 - lam P n X|) ∂P)
      + 24 * min (1 / Real.sqrt (lam P n X)) 1 * n * φ (m + 1) := by
  have hid := identity_2_6_core P n X hX hlam m h 1 hh
  have hXm := hX.1
  have hX1 := hX.2.2
  have hgood : ∀ᵐ ω ∂P, ∀ k, X k ω ≤ 1 := ae_all_iff.mpr hX1
  have hμ0 : 0 ≤ min (1 / Real.sqrt (lam P n X)) 1 := le_min (by positivity) zero_le_one
  have hl35 := l35_core (lam P n X) hlam h 1 hh
  have hS : ∀ k, |stein (lam P n X) h k| ≤ 4 * 1 * min (1 / Real.sqrt (lam P n X)) 1 := by
    intro k; rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp only [stein, Finset.range_zero, Finset.sum_empty, mul_zero, neg_zero, abs_zero]
      positivity
    · exact l33_core _ hlam h 1 hh k hk
  have h46 := lemma_4_6_core P n X hX φ hφ m (stein (lam P n X) h) _ hS
  have hT1 : |∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - ((j : ℕ) : ℤ)| ∧ |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
          ∫ ω, (X i ω : ℝ) * X j ω *
            delta (stein (lam P n X) h) (Y' n m X i ((j : ℤ) - 1) ω + 1) ∂P|
      ≤ 2 * (lam P n X)⁻¹ * (∑ i ∈ Finset.Icc 1 n,
          ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - ((j : ℕ) : ℤ)| ∧ |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
            ∫ ω, (X i ω : ℝ) * X j ω *
              (1 + 2 * min (1 / Real.sqrt (lam P n X)) 1 * |(Y' n m X i ((j : ℤ) - 1) ω : ℝ) + 1 - lam P n X|) ∂P) := by
    rw [mul_sum]; refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun i _ => ?_))
    rw [mul_sum]; refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun j _ => ?_))
    rw [← integral_const_mul]
    refine abs_int_le P ?_ ?_
    · have := integ_aux P (fun ω => (X i ω : ℝ) * X j ω) ((mcast _ (hXm i) _).mul (mcast _ (hXm j) _))
        (by filter_upwards [hX1 i, hX1 j] with ω h1 h2
            rw [abs_mul]; have := cast_le_one' _ h1; have := cast_le_one' _ h2
            calc _ ≤ (1:ℝ) * 1 := by gcongr
              _ = 1 := by ring)
        (Y' n m X i ((j : ℤ) - 1)) (meas_Y' n m X hXm i _) (2 * n)
        (by filter_upwards [hgood] with ω hx; exact_mod_cast Y'_le n m X ω hx i _)
        (2 * (lam P n X)⁻¹) (min (1 / Real.sqrt (lam P n X)) 1) (lam P n X)
      exact this
    · filter_upwards with ω
      have hD := hl35 (Y' n m X i ((j : ℤ) - 1) ω + 1) (by omega)
      push_cast at hD
      exact pt_bound _ _ _ _ _ (by positivity) hD
  have hT3 : |∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
          prob P X i * ∫ ω, (X j ω : ℝ) *
            delta (stein (lam P n X) h) (Y n m X i ((j : ℤ) - 1) ω + 1) ∂P|
      ≤ 2 * (lam P n X)⁻¹ * (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
            prob P X i * ∫ ω, (X j ω : ℝ) *
              (1 + 2 * min (1 / Real.sqrt (lam P n X)) 1 * |(Y n m X i ((j : ℤ) - 1) ω : ℝ) + 1 - lam P n X|) ∂P) := by
    rw [mul_sum]; refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun i _ => ?_))
    rw [mul_sum]; refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun j _ => ?_))
    have hp0 : 0 ≤ prob P X i := measureReal_nonneg
    rw [abs_mul, abs_of_nonneg hp0, mul_left_comm, ← integral_const_mul]
    apply mul_le_mul_of_nonneg_left _ hp0
    refine abs_int_le P ?_ ?_
    · exact integ_aux P (fun ω => (X j ω : ℝ)) (mcast _ (hXm j) _)
        (by filter_upwards [hX1 j] with ω h1; exact cast_le_one' _ h1)
        (Y n m X i ((j : ℤ) - 1)) (meas_Y n m X hXm i _) (2 * n)
        (by filter_upwards [hgood] with ω hx; exact_mod_cast Y_le n m X ω hx i _)
        (2 * (lam P n X)⁻¹) (min (1 / Real.sqrt (lam P n X)) 1) (lam P n X)
    · filter_upwards with ω
      have hD := hl35 (Y n m X i ((j : ℤ) - 1) ω + 1) (by omega)
      push_cast at hD
      exact pt_bound _ _ _ _ _ (by positivity) hD
  rw [hid]
  have e : ∀ a b c d : ℝ, a + b + c - d - a = b + c - d := fun a b c d => by ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
  have : 6 * (4 * 1 * min (1 / Real.sqrt (lam P n X)) 1) * n * φ (m + 1)
      = 24 * min (1 / Real.sqrt (lam P n X)) 1 * n * φ (m + 1) := by ring
  linarith


lemma sigmaIcc_le_Ici' {Ω β : Type*} [MeasurableSpace β] (X : ℕ → Ω → β) (a b : ℕ) :
    sigmaIcc X a b ≤ sigmaIci X a :=
  iSup₂_le fun i hi => le_iSup₂ (f := fun i (_ : i ∈ Set.Ici a) =>
    MeasurableSpace.comap (X i) inferInstance) i (Set.mem_Ici.mpr (Finset.mem_Icc.mp hi).1)

lemma sigmaIcc_mono' {Ω β : Type*} [MeasurableSpace β] (X : ℕ → Ω → β) (a b a' b' : ℕ)
    (ha : a' ≤ a) (hb : b ≤ b') : sigmaIcc X a b ≤ sigmaIcc X a' b' :=
  iSup₂_le fun i hi => le_iSup₂ (f := fun i (_ : i ∈ Finset.Icc a' b') =>
    MeasurableSpace.comap (X i) inferInstance) i (by simp only [Finset.mem_Icc] at hi ⊢; omega)

lemma int_nat_eq_sum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℕ) (hZ : Measurable Z) (N : ℕ) (hZN : ∀ᵐ ω ∂P, Z ω < N) :
    ∫ ω, (Z ω : ℝ) ∂P = ∑ z ∈ range N, (z:ℝ) * P.real {ω | Z ω = z} := by
  have : (fun ω => (Z ω : ℝ)) =ᵐ[P] fun ω => ∑ z ∈ range N, (z:ℝ) * {ω | Z ω = z}.indicator (fun _ => (1:ℝ)) ω := by
    filter_upwards [hZN] with ω hω
    rw [sum_eq_single (Z ω)]
    · simp [Set.indicator]
    · intro b _ hb; simp [Set.indicator, Ne.symm hb]
    · intro h; exact absurd (mem_range.mpr hω) h
  rw [integral_congr_ae this, integral_finset_sum]
  · apply sum_congr rfl; intro z _
    have hms : MeasurableSet {ω | Z ω = z} := hZ (measurableSet_singleton z)
    rw [integral_const_mul, integral_indicator hms, setIntegral_const]
    simp
  · intro z _; exact ((integrable_const _).indicator (hZ (measurableSet_singleton z))).const_mul _

lemma cov3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ)
    (m lo hi : ℕ) (hlo : 1 ≤ lo) (hlh : lo ≤ hi)
    (G : Ω → ℝ) (hG : Measurable[sigmaIcc X lo hi] G) (hG01 : ∀ᵐ ω ∂P, G ω = 0 ∨ G ω = 1)
    (L R : Ω → ℕ) (hL : L = fun ω => ∑ k ∈ Icc 1 n with k + m < lo, X k ω)
    (hR : R = fun ω => ∑ k ∈ Icc 1 n with hi + m < k, X k ω)
    (Vf : Ω → ℕ) (hVf : ∀ ω, Vf ω = L ω + R ω)
    (c : ℝ) (hc' : c = ∫ ω, (Vf ω : ℝ) ∂P) (hc0 : 0 ≤ c) (hcn : c ≤ n) :
    ∫ ω, |(Vf ω : ℝ) - c| * G ω ∂P
        - (∫ ω, |(Vf ω : ℝ) - c| ∂P) * ∫ ω, G ω ∂P
      ≤ 4 * n * (∫ ω, G ω ∂P) * φ (m + 1) + φ (m + 1) * (2 * c) := by
  simp only [hVf] at hc' ⊢
  obtain ⟨hXm, _, hX1⟩ := hX
  have hgood : ∀ᵐ ω ∂P, ∀ k, X k ω ≤ 1 := ae_all_iff.mpr hX1
  have hφ0 := phi_nonneg hφ (m + 1)
  have hhi : 1 ≤ hi := le_trans hlo hlh
  have hLm : Measurable[sigmaIcc X 1 hi] L := by
    rw [hL]; exact sum_meas_Icc X _ hi (by intro k hk; simp only [mem_filter, mem_Icc] at hk; omega)
  have hRm : Measurable[sigmaIci X (hi + (m + 1))] R := by
    rw [hR]; exact sum_meas_Ici X _ _ (by intro k hk; simp only [mem_filter, mem_Icc] at hk; omega)
  have hLm' : Measurable L := hLm.mono (sigmaIcc_le X hXm 1 hi) le_rfl
  have hRm' : Measurable R := hRm.mono (sigmaIci_le X hXm _) le_rfl
  have hG1 : Measurable[sigmaIcc X 1 hi] G := hG.mono (sigmaIcc_mono' X lo hi 1 hi hlo le_rfl) le_rfl
  have hGm : Measurable G := hG.mono (sigmaIcc_le X hXm lo hi) le_rfl
  have hGb : ∀ᵐ ω ∂P, |G ω| ≤ 1 := by
    filter_upwards [hG01] with ω h; rcases h with h | h <;> simp [h]
  have hG0 : ∀ᵐ ω ∂P, 0 ≤ G ω := by
    filter_upwards [hG01] with ω h; rcases h with h | h <;> simp [h]
  have iG : Integrable G P := integ_bdd P G hGm 1 hGb
  have hEG0 : 0 ≤ ∫ ω, G ω ∂P := integral_nonneg_of_ae hG0
  have hRN : ∀ᵐ ω ∂P, R ω < n + 1 := by
    filter_upwards [hgood] with ω hx
    have := sub_le_n n (fun k => X k ω) hx _ (filter_subset (fun k : ℕ => hi + m < k) (Icc 1 n))
    rw [hR]; simp only; omega
  have hLN : ∀ᵐ ω ∂P, L ω ≤ n := by
    filter_upwards [hgood] with ω hx
    have := sub_le_n n (fun k => X k ω) hx _ (filter_subset (fun k : ℕ => k + m < lo) (Icc 1 n))
    rw [hL]; simp only; omega
  have hLRn : ∀ᵐ ω ∂P, L ω + R ω ≤ n := by
    filter_upwards [hgood] with ω hx
    have := sub_le_n n (fun k => X k ω) hx ((Icc 1 n).filter (fun k => k + m < lo) ∪
      (Icc 1 n).filter (fun k => hi + m < k)) (union_subset (filter_subset _ _) (filter_subset _ _))
    rw [sum_union] at this
    · rw [hL, hR]; exact this
    · rw [disjoint_filter]; intro k _ h1 h2; omega
  set f : ℕ → ℕ → ℝ := fun a b => |((min (a + b) n : ℕ) : ℝ) - c| with hf
  have hfM : ∀ a b, |f a b| ≤ n := by
    intro a b; simp only [hf, abs_abs]
    have h1 : ((min (a + b) n : ℕ) : ℝ) ≤ n := by exact_mod_cast min_le_right _ _
    have h2 : (0:ℝ) ≤ ((min (a + b) n : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [abs_le]; constructor <;> linarith
  set fb : ℕ → ℝ := fun l => ∑ z ∈ range (n + 1), f l z * P.real {ω | R ω = z} with hfb
  have hF : ∀ᵐ ω ∂P, |((L ω + R ω : ℕ) : ℝ) - c| = f (L ω) (R ω) := by
    filter_upwards [hLRn] with ω h; simp only [hf, min_eq_left h]
  have d1 : |∫ ω, G ω * f (L ω) (R ω) ∂P - ∫ ω, G ω * fb (L ω) ∂P|
      ≤ 2 * n * φ (m + 1) * ∫ ω, |G ω| ∂P :=
    dec2 P X hXm φ hφ hi (m + 1) hhi (by omega) G hG1 1 hGb L hLm R hRm (n + 1) hRN f n hfM
  have d2 : |∫ ω, (fun _ => (1:ℝ)) ω * f (L ω) (R ω) ∂P - ∫ ω, (fun _ => (1:ℝ)) ω * fb (L ω) ∂P|
      ≤ 2 * n * φ (m + 1) * ∫ ω, |(fun _ => (1:ℝ)) ω| ∂P :=
    dec2 P X hXm φ hφ hi (m + 1) hhi (by omega) (fun _ => 1) measurable_const 1
      (Filter.Eventually.of_forall (fun _ => by simp)) L hLm R hRm (n + 1) hRN f n hfM
  simp only [one_mul, abs_one, integral_const, probReal_univ, smul_eq_mul, mul_one] at d2
  have hfbM : ∀ l, |fb l| ≤ n := fun l => gbar_le P R hRm' (n + 1) (f l) n (fun z => hfM l z)
  have hER := int_nat_eq_sum P R hRm' (n + 1) hRN
  have hfb0 : ∀ l, 0 ≤ fb l := fun l =>
    sum_nonneg (fun z _ => mul_nonneg (abs_nonneg _) measureReal_nonneg)
  have hfb_le : ∀ l, fb l ≤ l + c + ∫ ω, (R ω : ℝ) ∂P := by
    intro l
    rw [hER]
    have hs := sum_preal_le_one P R hRm' (range (n + 1))
    calc fb l ≤ ∑ z ∈ range (n + 1), ((l:ℝ) + c + z) * P.real {ω | R ω = z} := by
          apply sum_le_sum; intro z _
          apply mul_le_mul_of_nonneg_right _ measureReal_nonneg
          simp only [hf]
          have h1 : ((min (l + z) n : ℕ) : ℝ) ≤ l + z := by exact_mod_cast min_le_left _ _
          have h2 : (0:ℝ) ≤ ((min (l + z) n : ℕ) : ℝ) := Nat.cast_nonneg _
          rw [abs_le]; constructor <;> linarith
      _ = ((l:ℝ) + c) * ∑ z ∈ range (n + 1), P.real {ω | R ω = z}
            + ∑ z ∈ range (n + 1), (z:ℝ) * P.real {ω | R ω = z} := by
          rw [mul_sum, ← sum_add_distrib]; apply sum_congr rfl; intro z _; ring
      _ ≤ ((l:ℝ) + c) * 1 + ∑ z ∈ range (n + 1), (z:ℝ) * P.real {ω | R ω = z} := by
          have := mul_le_mul_of_nonneg_left hs (add_nonneg (Nat.cast_nonneg l) hc0)
          linarith
      _ = _ := by ring
  have hfbm : Measurable (fun ω => fb (L ω)) := (measurable_from_top (f := fb)).comp hLm'
  have ifb : Integrable (fun ω => fb (L ω)) P :=
    integ_bdd P _ hfbm n (Filter.Eventually.of_forall (fun ω => hfbM _))
  have iL : Integrable (fun ω => (L ω : ℝ)) P := integ_bdd P _ (mcast _ hLm' _) n (by
    filter_upwards [hLN] with ω h; rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast h)
  have iR : Integrable (fun ω => (R ω : ℝ)) P := integ_bdd P _ (mcast _ hRm' _) n (by
    filter_upwards [hRN] with ω h; rw [abs_of_nonneg (Nat.cast_nonneg _)]
    have : R ω ≤ n := by omega
    exact_mod_cast this)
  have hc : c = ∫ ω, (L ω : ℝ) ∂P + ∫ ω, (R ω : ℝ) ∂P := by
    rw [hc', ← integral_add iL iR]; congr 1; funext ω; push_cast; ring
  have hfbint : ∫ ω, |fb (L ω)| ∂P ≤ 2 * c := by
    calc ∫ ω, |fb (L ω)| ∂P ≤ ∫ ω, ((L ω : ℝ) + (c + ∫ ω, (R ω : ℝ) ∂P)) ∂P := by
          apply integral_mono ifb.abs (iL.add (integrable_const _))
          intro ω; simp only [Pi.add_apply]; rw [abs_of_nonneg (hfb0 _)]; have := hfb_le (L ω); linarith
      _ = 2 * c := by
          rw [integral_add iL (integrable_const _), integral_const]; simp; linarith
  have d3 : (∫ ω, fb (L ω) * G ω ∂P) - (∫ ω, fb (L ω) ∂P) * ∫ ω, G ω ∂P ≤ φ (m + 1) * (2 * c) := by
    rcases le_or_gt lo (m + 1) with hsm | hbg
    · have hL0 : ∀ ω, L ω = 0 := by
        intro ω; rw [hL]; apply sum_eq_zero; intro k hk
        simp only [mem_filter, mem_Icc] at hk; omega
      have : (∫ ω, fb (L ω) * G ω ∂P) - (∫ ω, fb (L ω) ∂P) * ∫ ω, G ω ∂P = 0 := by
        simp only [hL0, integral_const_mul, integral_const, probReal_univ, smul_eq_mul, one_mul]
        ring
      rw [this]; exact mul_nonneg hφ0 (by linarith)
    · have hLj : Measurable[sigmaIcc X 1 (lo - (m + 1))] L := by
        rw [hL]; exact sum_meas_Icc X _ _ (by
          intro k hk; simp only [mem_filter, mem_Icc] at hk; omega)
      have hU : Measurable[sigmaIcc X 1 (lo - (m + 1))] (fun ω => fb (L ω)) :=
        (measurable_from_top (f := fb)).comp hLj
      have hB : MeasurableSet[sigmaIci X (lo - (m + 1) + (m + 1))] {ω | G ω = 1} := by
        have : lo - (m + 1) + (m + 1) = lo := by omega
        rw [this]; exact (sigmaIcc_le_Ici' X lo hi) _ (hG (measurableSet_singleton 1))
      have mx := mix_U P X hXm φ hφ (lo - (m + 1)) (m + 1) (by omega) (fun ω => fb (L ω)) hU n
        (Filter.Eventually.of_forall (fun ω => hfbM _)) _ hB
      have eG : (fun ω => {ω | G ω = 1}.indicator (fun _ => (1:ℝ)) ω) =ᵐ[P] G := by
        filter_upwards [hG01] with ω h; rcases h with h | h <;> simp [Set.indicator, h]
      have e1 : ∫ ω, fb (L ω) * {ω | G ω = 1}.indicator (fun _ => (1:ℝ)) ω ∂P
          = ∫ ω, fb (L ω) * G ω ∂P := by
        apply integral_congr_ae; filter_upwards [eG] with ω h; rw [h]
      have e2 : P.real {ω | G ω = 1} = ∫ ω, G ω ∂P := by
        have hms : MeasurableSet {ω | G ω = 1} := hGm (measurableSet_singleton 1)
        rw [← integral_congr_ae eG, integral_indicator hms, setIntegral_const]; simp
      try simp only at mx
      rw [e1, e2] at mx
      have := mul_le_mul_of_nonneg_left hfbint hφ0
      linarith [le_abs_self ((∫ ω, fb (L ω) * G ω ∂P) - (∫ ω, fb (L ω) ∂P) * ∫ ω, G ω ∂P)]
  have eA1 : ∫ ω, |((L ω + R ω : ℕ) : ℝ) - c| * G ω ∂P = ∫ ω, G ω * f (L ω) (R ω) ∂P := by
    apply integral_congr_ae; filter_upwards [hF] with ω h; rw [h, mul_comm]
  have eA2 : ∫ ω, |((L ω + R ω : ℕ) : ℝ) - c| ∂P = ∫ ω, f (L ω) (R ω) ∂P := by
    apply integral_congr_ae; filter_upwards [hF] with ω h; rw [h]
  have e3 : ∫ ω, G ω * fb (L ω) ∂P = ∫ ω, fb (L ω) * G ω ∂P := by
    congr 1; funext ω; ring
  have eGa : ∫ ω, |G ω| ∂P = ∫ ω, G ω ∂P := by
    apply integral_congr_ae; filter_upwards [hG0] with ω h; rw [abs_of_nonneg h]
  rw [e3, eGa] at d1
  rw [eA1, eA2]
  have h4 : (∫ ω, G ω ∂P) * ((∫ ω, fb (L ω) ∂P) - ∫ ω, f (L ω) (R ω) ∂P)
      ≤ (∫ ω, G ω ∂P) * (2 * n * φ (m + 1)) := by
    apply mul_le_mul_of_nonneg_left _ hEG0
    rw [abs_sub_comm] at d2
    exact (le_abs_self _).trans d2
  have h5 := le_abs_self (∫ ω, G ω * f (L ω) (R ω) ∂P - ∫ ω, fb (L ω) * G ω ∂P)
  nlinarith


lemma Vij_split (n m : ℕ) {Ω : Type*} (X : ℕ → Ω → ℕ) (i j : ℕ) (hij : |(i : ℤ) - (j : ℤ)| ≤ m)
    (ω : Ω) :
    Vij n m X i j ω = (∑ k ∈ Icc 1 n with k + m < min i j, X k ω)
      + ∑ k ∈ Icc 1 n with max i j + m < k, X k ω := by
  rw [abs_le] at hij
  unfold Vij
  simp only [sum_filter, ← sum_add_distrib]
  apply sum_congr rfl; intro k _
  split_ifs <;> omega

lemma card_two_Icc (S : Finset ℕ) (a b c d : ℕ) (h : ∀ k ∈ S, (a ≤ k ∧ k ≤ b) ∨ (c ≤ k ∧ k ≤ d)) :
    S.card ≤ (b + 1 - a) + (d + 1 - c) := by
  have hsub : S ⊆ Icc a b ∪ Icc c d := by
    intro k hk; rw [mem_union, mem_Icc, mem_Icc]; exact h k hk
  calc S.card ≤ (Icc a b ∪ Icc c d).card := card_le_card hsub
    _ ≤ (Icc a b).card + (Icc c d).card := card_union_le _ _
    _ = _ := by rw [Nat.card_Icc, Nat.card_Icc]

lemma sum_le_card' (x : ℕ → ℕ) (hx : ∀ k, x k ≤ 1) (S : Finset ℕ) : ∑ k ∈ S, x k ≤ S.card := by
  calc ∑ k ∈ S, x k ≤ ∑ k ∈ S, 1 := sum_le_sum (fun k _ => hx k)
    _ = S.card := by simp

lemma Y_split (n m : ℕ) {Ω : Type*} (X : ℕ → Ω → ℕ) (i j : ℕ) (hij : |(i : ℤ) - (j : ℤ)| ≤ m)
    (ω : Ω) :
    Y n m X i ((j : ℤ) - 1) ω = Vij n m X i j ω + ∑ k ∈ Icc 1 n with
      ((m < Int.natAbs (((k : ℕ) : ℤ) - i) ∨ ((i : ℤ) - m ≤ ((k : ℕ) : ℤ) ∧ ((k : ℕ) : ℤ) ≤ (j : ℤ) - 1))
        ∧ ¬ (m < Int.natAbs (((k : ℕ) : ℤ) - i) ∧ m < Int.natAbs (((k : ℕ) : ℤ) - j))), X k ω := by
  rw [abs_le] at hij
  unfold Y V Vij
  simp only [sum_filter, ← sum_add_distrib]
  apply sum_congr rfl; intro k _
  split_ifs <;> omega

lemma Y_bounds (n m : ℕ) {Ω : Type*} (X : ℕ → Ω → ℕ) (i j : ℕ) (hi1 : 1 ≤ i) (hj1 : 1 ≤ j)
    (hij : |(i : ℤ) - (j : ℤ)| ≤ m) (ω : Ω) (hx : ∀ k, X k ω ≤ 1) :
    Vij n m X i j ω ≤ Y' n m X i ((j : ℤ) - 1) ω ∧
      Y' n m X i ((j : ℤ) - 1) ω ≤ Y n m X i ((j : ℤ) - 1) ω ∧
      Y n m X i ((j : ℤ) - 1) ω ≤ Vij n m X i j ω + 3 * m := by
  have h1 : Vij n m X i j ω ≤ V n m X i ω := by
    unfold Vij V; apply sum_le_sum_of_subset; intro k; simp only [mem_filter]; tauto
  refine ⟨?_, ?_, ?_⟩
  · unfold Y'; omega
  · unfold Y' Y; apply Nat.add_le_add_left; apply sum_le_sum_of_subset
    intro k; simp only [mem_filter]; tauto
  · rw [Y_split n m X i j hij ω]
    apply Nat.add_le_add_left
    refine (sum_le_card' (fun k => X k ω) hx _).trans ?_
    have hij' := abs_le.mp hij
    rcases le_or_gt i j with hle | hlt
    · have := card_two_Icc ((Icc 1 n).filter (fun k : ℕ =>
        ((m < Int.natAbs (((k : ℕ) : ℤ) - i) ∨ ((i : ℤ) - m ≤ ((k : ℕ) : ℤ) ∧ ((k : ℕ) : ℤ) ≤ (j : ℤ) - 1))
        ∧ ¬ (m < Int.natAbs (((k : ℕ) : ℤ) - i) ∧ m < Int.natAbs (((k : ℕ) : ℤ) - j)))))
        (i - m) (j - 1) (i + m + 1) (j + m) (by
          intro k hk; simp only [mem_filter, mem_Icc] at hk; omega)
      omega
    · have := card_two_Icc ((Icc 1 n).filter (fun k : ℕ =>
        ((m < Int.natAbs (((k : ℕ) : ℤ) - i) ∨ ((i : ℤ) - m ≤ ((k : ℕ) : ℤ) ∧ ((k : ℕ) : ℤ) ≤ (j : ℤ) - 1))
        ∧ ¬ (m < Int.natAbs (((k : ℕ) : ℤ) - i) ∧ m < Int.natAbs (((k : ℕ) : ℤ) - j)))))
        (j - m) (j - 1) 1 0 (by
          intro k hk; simp only [mem_filter, mem_Icc] at hk; omega)
      omega

lemma EV_facts {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (m i j : ℕ)
    (hij : |(i : ℤ) - (j : ℤ)| ≤ m) :
    0 ≤ ∫ ω, (Vij n m X i j ω : ℝ) ∂P ∧ ∫ ω, (Vij n m X i j ω : ℝ) ∂P ≤ lam P n X ∧
      lam P n X ≤ n ∧ lam P n X ≤ ∫ ω, (Vij n m X i j ω : ℝ) ∂P + (3 * m + 1) := by
  obtain ⟨hXm, _, hX1⟩ := hX
  have hc : ∫ ω, (Vij n m X i j ω : ℝ) ∂P = ∑ k ∈ Icc 1 n with
      (m < Int.natAbs (((k : ℕ) : ℤ) - i) ∧ m < Int.natAbs (((k : ℕ) : ℤ) - j)), prob P X k := by
    simp only [Vij]; push_cast
    rw [integral_finset_sum _ (fun k _ => integ_X P X hXm hX1 k)]
    exact sum_congr rfl (fun k _ => int_X P X hXm hX1 k)
  rw [hc]
  have hp0 : ∀ k, 0 ≤ prob P X k := fun k => measureReal_nonneg
  have hp1 : ∀ k, prob P X k ≤ 1 := fun k => measureReal_le_one
  refine ⟨sum_nonneg (fun k _ => hp0 k), ?_, ?_, ?_⟩
  · unfold lam; exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun k _ _ => hp0 k)
  · unfold lam
    calc ∑ k ∈ Icc 1 n, prob P X k ≤ ∑ k ∈ Icc 1 n, (1:ℝ) := sum_le_sum (fun k _ => hp1 k)
      _ = n := by simp
  · unfold lam
    rw [← sum_filter_add_sum_filter_not (Icc 1 n) (fun k : ℕ =>
      m < Int.natAbs (((k : ℕ) : ℤ) - i) ∧ m < Int.natAbs (((k : ℕ) : ℤ) - j))]
    have h1 : ∑ k ∈ (Icc 1 n).filter (fun k : ℕ =>
        ¬ (m < Int.natAbs (((k : ℕ) : ℤ) - i) ∧ m < Int.natAbs (((k : ℕ) : ℤ) - j))), prob P X k
        ≤ ((Icc 1 n).filter (fun k : ℕ =>
        ¬ (m < Int.natAbs (((k : ℕ) : ℤ) - i) ∧ m < Int.natAbs (((k : ℕ) : ℤ) - j)))).card := by
      calc _ ≤ ∑ k ∈ (Icc 1 n).filter (fun k : ℕ =>
            ¬ (m < Int.natAbs (((k : ℕ) : ℤ) - i) ∧ m < Int.natAbs (((k : ℕ) : ℤ) - j))), (1:ℝ) :=
            sum_le_sum (fun k _ => hp1 k)
        _ = _ := by simp
    have h2 : ((Icc 1 n).filter (fun k : ℕ =>
        ¬ (m < Int.natAbs (((k : ℕ) : ℤ) - i) ∧ m < Int.natAbs (((k : ℕ) : ℤ) - j)))).card ≤ 3 * m + 1 := by
      have hij' := abs_le.mp hij
      have hsub : (Icc 1 n).filter (fun k : ℕ =>
          ¬ (m < Int.natAbs (((k : ℕ) : ℤ) - i) ∧ m < Int.natAbs (((k : ℕ) : ℤ) - j)))
          ⊆ Icc (min i j - m) (max i j + m) := by
        intro k hk; simp only [mem_filter, mem_Icc] at hk ⊢; omega
      have := card_le_card hsub
      rw [Nat.card_Icc] at this; omega
    have h2' : ((((Icc 1 n).filter (fun k : ℕ =>
        ¬ (m < Int.natAbs (((k : ℕ) : ℤ) - i) ∧ m < Int.natAbs (((k : ℕ) : ℤ) - j)))).card : ℕ) : ℝ)
        ≤ 3 * m + 1 := by exact_mod_cast h2
    linarith

lemma covV {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ)
    (m i j : ℕ) (hi : i ∈ Icc 1 n) (hj : j ∈ Icc 1 n) (hij : |(i : ℤ) - (j : ℤ)| ≤ m)
    (G : Ω → ℝ) (hG : Measurable[sigmaIcc X (min i j) (max i j)] G)
    (hG01 : ∀ᵐ ω ∂P, G ω = 0 ∨ G ω = 1) :
    ∫ ω, |(Vij n m X i j ω : ℝ) - ∫ ω', (Vij n m X i j ω' : ℝ) ∂P| * G ω ∂P
        - (∫ ω, |(Vij n m X i j ω : ℝ) - ∫ ω', (Vij n m X i j ω' : ℝ) ∂P| ∂P) * ∫ ω, G ω ∂P
      ≤ 4 * n * (∫ ω, G ω ∂P) * φ (m + 1) + φ (m + 1) * (2 * lam P n X) := by
  obtain ⟨hc0, hcl, hln, -⟩ := EV_facts P n X hX m i j hij
  have hφ0 := phi_nonneg hφ (m + 1)
  have h3 := cov3 P n X hX φ hφ m (min i j) (max i j)
    (le_min (mem_Icc.mp hi).1 (mem_Icc.mp hj).1) min_le_max G hG hG01 _ _ rfl rfl
    (Vij n m X i j) (fun ω => Vij_split n m X i j hij ω) _ rfl hc0 (hcl.trans hln)
  have := mul_le_mul_of_nonneg_left hcl hφ0
  linarith

lemma Gpair_meas {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℕ) (i j : ℕ) :
    Measurable[sigmaIcc X (min i j) (max i j)] (fun ω => (X i ω : ℝ) * X j ω) :=
  ((measurable_from_top (f := fun k : ℕ => (k : ℝ))).comp
    (X_meas_Icc X _ _ i ⟨min_le_left _ _, le_max_left _ _⟩)).mul
  ((measurable_from_top (f := fun k : ℕ => (k : ℝ))).comp
    (X_meas_Icc X _ _ j ⟨min_le_right _ _, le_max_right _ _⟩))

lemma Gsingle_meas {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℕ) (i j : ℕ) :
    Measurable[sigmaIcc X (min i j) (max i j)] (fun ω => (X j ω : ℝ)) :=
  (measurable_from_top (f := fun k : ℕ => (k : ℝ))).comp
    (X_meas_Icc X _ _ j ⟨min_le_right _ _, le_max_right _ _⟩)

theorem bound_4_17_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ) (m : ℕ) (i j : ℕ)
    (hi : i ∈ Finset.Icc 1 n) (hj : j ∈ Finset.Icc 1 n)
    (hij : 0 < |(i : ℤ) - ((j : ℕ) : ℤ)| ∧ |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m) :
    cov[fun ω => |(Vij n m X i j ω : ℝ) - ∫ ω', (Vij n m X i j ω' : ℝ) ∂P|,
        fun ω => (X i ω : ℝ) * X j ω; P]
      ≤ 4 * n * prob P X i * φ (m + 1) + 4 * lam P n X * φ (m + 1) := by
  have hXm := hX.1; have hX1 := hX.2.2
  have hgood : ∀ᵐ ω ∂P, ∀ k, X k ω ≤ 1 := ae_all_iff.mpr hX1
  have hφ0 := phi_nonneg hφ (m + 1)
  obtain ⟨hc0, hcl, hln, -⟩ := EV_facts P n X hX m i j hij.2
  have hl0 : 0 ≤ lam P n X := hc0.trans hcl
  have hG01 : ∀ᵐ ω ∂P, (X i ω : ℝ) * X j ω = 0 ∨ (X i ω : ℝ) * X j ω = 1 := by
    filter_upwards [hX1 i, hX1 j] with ω h1 h2
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with a | a <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h2 with b | b <;> simp [a, b]
  have h := covV P n X hX φ hφ m i j hi hj hij.2 _ (Gpair_meas X i j) hG01
  have hVm : Measurable (fun ω => (Vij n m X i j ω : ℝ)) := by
    apply mcast; unfold Vij; exact Finset.measurable_sum _ (fun k _ => hXm k)
  have hVn : ∀ᵐ ω ∂P, Vij n m X i j ω ≤ n := by
    filter_upwards [hgood] with ω hx; exact sub_le_n n (fun k => X k ω) hx _ (filter_subset _ _)
  have hF : MemLp (fun ω => |(Vij n m X i j ω : ℝ) - ∫ ω', (Vij n m X i j ω' : ℝ) ∂P|) 2 P := by
    refine MemLp.of_bound ((hVm.sub measurable_const).abs).aestronglyMeasurable
      (n + |∫ ω', (Vij n m X i j ω' : ℝ) ∂P|) ?_
    filter_upwards [hVn] with ω h
    rw [Real.norm_eq_abs, abs_abs]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    have : ((Vij n m X i j ω : ℕ) : ℝ) ≤ n := by exact_mod_cast h
    linarith
  have hGm : Measurable (fun ω => (X i ω : ℝ) * X j ω) := (mcast _ (hXm i) _).mul (mcast _ (hXm j) _)
  have hGL : MemLp (fun ω => (X i ω : ℝ) * X j ω) 2 P := by
    refine MemLp.of_bound hGm.aestronglyMeasurable 1 ?_
    filter_upwards [hG01] with ω h; rcases h with h | h <;> simp [h]
  rw [covariance_eq_sub hF hGL]
  simp only [Pi.mul_apply]
  have hEG : ∫ ω, (X i ω : ℝ) * X j ω ∂P ≤ prob P X i := by
    rw [← int_X P X hXm hX1 i]
    apply integral_mono_ae (hGL.integrable (by norm_num)) (integ_X P X hXm hX1 i)
    filter_upwards [hX1 i, hX1 j] with ω h1 h2
    have : (X j ω : ℝ) ≤ 1 := by exact_mod_cast h2
    have : (0 : ℝ) ≤ X i ω := Nat.cast_nonneg _
    nlinarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h4 : 4 * n * (∫ ω, (X i ω : ℝ) * X j ω ∂P) * φ (m + 1) ≤ 4 * n * prob P X i * φ (m + 1) := by
    apply mul_le_mul_of_nonneg_right _ hφ0
    exact mul_le_mul_of_nonneg_left hEG (by positivity)
  have h5 : φ (m + 1) * (2 * lam P n X) ≤ 4 * lam P n X * φ (m + 1) := by nlinarith
  linarith


lemma pt_Y (v y c l : ℝ) (m : ℕ) (h1 : v ≤ y) (h2 : y ≤ v + 3 * m) (h3 : c ≤ l) (h4 : l ≤ c + (3 * m + 1)) :
    |y + 1 - l| ≤ |v - c| + (3 * m + 1) := by
  have a1 := le_abs_self (v - c)
  have a2 := neg_abs_le (v - c)
  rw [abs_le]; constructor <;> linarith

lemma core_YB {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ)
    (m i j : ℕ) (hi : i ∈ Icc 1 n) (hj : j ∈ Icc 1 n) (hij : |(i : ℤ) - (j : ℤ)| ≤ m)
    (G : Ω → ℝ) (hG : Measurable[sigmaIcc X (min i j) (max i j)] G)
    (hG01 : ∀ᵐ ω ∂P, G ω = 0 ∨ G ω = 1)
    (Yv : Ω → ℕ) (hYm : Measurable Yv)
    (hYv : ∀ᵐ ω ∂P, Vij n m X i j ω ≤ Yv ω ∧ Yv ω ≤ Vij n m X i j ω + 3 * m) :
    ∫ ω, G ω * (1 + 2 * min (1 / Real.sqrt (lam P n X)) 1 * |(Yv ω : ℝ) + 1 - lam P n X|) ∂P
      ≤ (∫ ω, G ω ∂P) * (8 * m + 5 + 4 * Real.sqrt ((n : ℝ) * φ (m + 1)))
        + 2 * min (1 / Real.sqrt (lam P n X)) 1 *
          (4 * n * (∫ ω, G ω ∂P) * φ (m + 1) + φ (m + 1) * (2 * lam P n X)) := by
  have hXm := hX.1; have hX1 := hX.2.2
  have hgood : ∀ᵐ ω ∂P, ∀ k, X k ω ≤ 1 := ae_all_iff.mpr hX1
  have hφ0 := phi_nonneg hφ (m + 1)
  obtain ⟨hc0, hcl, hln, hlc⟩ := EV_facts P n X hX m i j hij
  have hcov := covV P n X hX φ hφ m i j hi hj hij G hG hG01
  have hA := (bound_4_16_core P n X hX φ hφ m i j)
  have hA' := hA.1.trans hA.2
  set lm := lam P n X with hlm
  set μ := min (1 / Real.sqrt lm) 1 with hμ
  set c := ∫ ω', (Vij n m X i j ω' : ℝ) ∂P with hc
  set K0 := (m : ℝ) + 1 + 2 * Real.sqrt ((n : ℝ) * φ (m + 1)) with hK0
  set A := ∫ ω, |(Vij n m X i j ω : ℝ) - c| ∂P with hAdef
  have hl0 : 0 ≤ lm := hc0.trans hcl
  have hμ0 : 0 ≤ μ := le_min (by positivity) zero_le_one
  have hμ1 : μ ≤ 1 := min_le_right _ _
  have hμl : μ * Real.sqrt lm ≤ 1 := by
    rcases eq_or_lt_of_le hl0 with h | h
    · rw [← h, Real.sqrt_zero, mul_zero]; exact zero_le_one
    · have hs : 0 < Real.sqrt lm := Real.sqrt_pos.mpr h
      calc μ * Real.sqrt lm ≤ (1 / Real.sqrt lm) * Real.sqrt lm :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hs.le
        _ = 1 := by field_simp
  have hK00 : 0 ≤ K0 := by positivity
  have hGm : Measurable G := hG.mono (sigmaIcc_le X hXm _ _) le_rfl
  have hGb : ∀ᵐ ω ∂P, |G ω| ≤ 1 := by
    filter_upwards [hG01] with ω h; rcases h with h | h <;> simp [h]
  have hG0 : ∀ᵐ ω ∂P, 0 ≤ G ω := by
    filter_upwards [hG01] with ω h; rcases h with h | h <;> simp [h]
  have iG : Integrable G P := integ_bdd P G hGm 1 hGb
  have hEG0 : 0 ≤ ∫ ω, G ω ∂P := integral_nonneg_of_ae hG0
  have hVm : Measurable (fun ω => (Vij n m X i j ω : ℝ)) := by
    apply mcast; unfold Vij; exact Finset.measurable_sum _ (fun k _ => hXm k)
  have hVn : ∀ᵐ ω ∂P, Vij n m X i j ω ≤ n := by
    filter_upwards [hgood] with ω hx; exact sub_le_n n (fun k => X k ω) hx _ (filter_subset _ _)
  have iV : Integrable (fun ω => (Vij n m X i j ω : ℝ)) P := integ_bdd P _ hVm n (by
    filter_upwards [hVn] with ω h; rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast h)
  have iVG : Integrable (fun ω => |(Vij n m X i j ω : ℝ) - c| * G ω) P := by
    have := ((iV.sub (integrable_const c)).abs).bdd_mul hGm.aestronglyMeasurable
      (by filter_upwards [hGb] with ω h; simpa using h)
    exact this.congr (Filter.Eventually.of_forall (fun ω => by simp only [Pi.sub_apply]; ring))
  have iL : Integrable (fun ω => G ω * (1 + 2 * μ * |(Yv ω : ℝ) + 1 - lm|)) P := by
    have := integ_aux P G hGm hGb Yv hYm (n + 3 * m) (by
      filter_upwards [hYv, hVn] with ω h1 h2
      have : Yv ω ≤ n + 3 * m := by omega
      exact_mod_cast this) 1 μ lm
    simpa only [one_mul] using this
  have iR : Integrable (fun ω => (1 + 2 * μ * (3 * m + 1)) * G ω
      + 2 * μ * (|(Vij n m X i j ω : ℝ) - c| * G ω)) P :=
    (iG.const_mul _).add (iVG.const_mul _)
  have hmono : ∫ ω, G ω * (1 + 2 * μ * |(Yv ω : ℝ) + 1 - lm|) ∂P
      ≤ ∫ ω, ((1 + 2 * μ * (3 * m + 1)) * G ω
        + 2 * μ * (|(Vij n m X i j ω : ℝ) - c| * G ω)) ∂P := by
    apply integral_mono_ae iL iR
    filter_upwards [hYv, hG0] with ω h hg
    have hv1 : ((Vij n m X i j ω : ℕ) : ℝ) ≤ Yv ω := by exact_mod_cast h.1
    have hv2 : ((Yv ω : ℕ) : ℝ) ≤ (Vij n m X i j ω : ℝ) + 3 * m := by exact_mod_cast h.2
    have hp := pt_Y _ _ _ _ m hv1 hv2 hcl hlc
    have := mul_le_mul_of_nonneg_left hp (mul_nonneg (mul_nonneg zero_le_two hμ0) hg)
    nlinarith
  rw [integral_add (iG.const_mul _) (iVG.const_mul _), integral_const_mul, integral_const_mul] at hmono
  have hJ := hcov
  have e1 : μ * (3 * m + 1) * (∫ ω, G ω ∂P) ≤ (3 * m + 1) * ∫ ω, G ω ∂P :=
    mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (by positivity) hμ1) hEG0
  have e2 : μ * A * (∫ ω, G ω ∂P) ≤ K0 * ∫ ω, G ω ∂P := by
    apply mul_le_mul_of_nonneg_right _ hEG0
    calc μ * A ≤ μ * (Real.sqrt lm * K0) := mul_le_mul_of_nonneg_left hA' hμ0
      _ = (μ * Real.sqrt lm) * K0 := by ring
      _ ≤ 1 * K0 := mul_le_mul_of_nonneg_right hμl hK00
      _ = K0 := one_mul K0
  have e3 : μ * ((∫ ω, |(Vij n m X i j ω : ℝ) - c| * G ω ∂P) - A * ∫ ω, G ω ∂P)
      ≤ μ * (4 * n * (∫ ω, G ω ∂P) * φ (m + 1) + φ (m + 1) * (2 * lm)) :=
    mul_le_mul_of_nonneg_left hJ hμ0
  rw [hK0] at e2
  nlinarith

theorem bound_4_18_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ) (m : ℕ) (i j : ℕ)
    (hi : i ∈ Finset.Icc 1 n) (hj : j ∈ Finset.Icc 1 n)
    (hij : 0 < |(i : ℤ) - ((j : ℕ) : ℤ)| ∧ |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m) :
    ∫ ω, (X i ω : ℝ) * X j ω *
        (1 + 2 * min (1 / Real.sqrt (lam P n X)) 1 * |(Y' n m X i ((j : ℤ) - 1) ω : ℝ) + 1 - lam P n X|) ∂P
      ≤ (∫ ω, (X i ω : ℝ) * X j ω ∂P) * (8 * m + 5 + 4 * Real.sqrt ((n : ℝ) * φ (m + 1)))
        + 8 * min (1 / Real.sqrt (lam P n X)) 1 * (n * prob P X i + lam P n X) * φ (m + 1) := by
  have hXm := hX.1; have hX1 := hX.2.2
  have hgood : ∀ᵐ ω ∂P, ∀ k, X k ω ≤ 1 := ae_all_iff.mpr hX1
  have hφ0 := phi_nonneg hφ (m + 1)
  obtain ⟨hc0, hcl, hln, -⟩ := EV_facts P n X hX m i j hij.2
  have hl0 : 0 ≤ lam P n X := hc0.trans hcl
  have hμ0 : 0 ≤ min (1 / Real.sqrt (lam P n X)) 1 := le_min (by positivity) zero_le_one
  have hG01 : ∀ᵐ ω ∂P, (X i ω : ℝ) * X j ω = 0 ∨ (X i ω : ℝ) * X j ω = 1 := by
    filter_upwards [hX1 i, hX1 j] with ω h1 h2
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with a | a <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h2 with b | b <;> simp [a, b]
  have hYv : ∀ᵐ ω ∂P, Vij n m X i j ω ≤ Y' n m X i ((j : ℤ) - 1) ω ∧
      Y' n m X i ((j : ℤ) - 1) ω ≤ Vij n m X i j ω + 3 * m := by
    filter_upwards [hgood] with ω hx
    obtain ⟨b1, b2, b3⟩ := Y_bounds n m X i j (mem_Icc.mp hi).1 (mem_Icc.mp hj).1 hij.2 ω hx
    exact ⟨b1, b2.trans b3⟩
  have h := core_YB P n X hX φ hφ m i j hi hj hij.2 _ (Gpair_meas X i j) hG01 _
    (meas_Y' n m X hXm i _) hYv
  have hGm : Measurable (fun ω => (X i ω : ℝ) * X j ω) := (mcast _ (hXm i) _).mul (mcast _ (hXm j) _)
  have hEG : ∫ ω, (X i ω : ℝ) * X j ω ∂P ≤ prob P X i := by
    rw [← int_X P X hXm hX1 i]
    apply integral_mono_ae (integ_bdd P _ hGm 1 (by
      filter_upwards [hG01] with ω h; rcases h with h | h <;> simp [h])) (integ_X P X hXm hX1 i)
    filter_upwards [hX1 i, hX1 j] with ω h1 h2
    have : (X j ω : ℝ) ≤ 1 := by exact_mod_cast h2
    have : (0 : ℝ) ≤ X i ω := Nat.cast_nonneg _
    nlinarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h4 : 4 * n * (∫ ω, (X i ω : ℝ) * X j ω ∂P) * φ (m + 1) ≤ 4 * n * prob P X i * φ (m + 1) := by
    apply mul_le_mul_of_nonneg_right _ hφ0
    exact mul_le_mul_of_nonneg_left hEG (by positivity)
  have h5 : 2 * min (1 / Real.sqrt (lam P n X)) 1 *
      (4 * n * (∫ ω, (X i ω : ℝ) * X j ω ∂P) * φ (m + 1) + φ (m + 1) * (2 * lam P n X))
      ≤ 8 * min (1 / Real.sqrt (lam P n X)) 1 * (n * prob P X i + lam P n X) * φ (m + 1) := by
    have h6 : 4 * n * (∫ ω, (X i ω : ℝ) * X j ω ∂P) * φ (m + 1) + φ (m + 1) * (2 * lam P n X)
        ≤ 4 * ((n * prob P X i + lam P n X) * φ (m + 1)) := by nlinarith
    have := mul_le_mul_of_nonneg_left h6 (mul_nonneg zero_le_two hμ0)
    linarith
  have e : ∀ ω, (X i ω : ℝ) * X j ω *
      (1 + 2 * min (1 / Real.sqrt (lam P n X)) 1 * |(Y' n m X i ((j : ℤ) - 1) ω : ℝ) + 1 - lam P n X|)
      = (fun ω => (X i ω : ℝ) * X j ω) ω *
      (1 + 2 * min (1 / Real.sqrt (lam P n X)) 1 * |(Y' n m X i ((j : ℤ) - 1) ω : ℝ) + 1 - lam P n X|) :=
    fun ω => rfl
  simp only [e]
  linarith

theorem bound_4_19_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ) (m : ℕ) (i j : ℕ)
    (hi : i ∈ Finset.Icc 1 n) (hj : j ∈ Finset.Icc 1 n) (hij : |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m) :
    prob P X i * ∫ ω, (X j ω : ℝ) *
        (1 + 2 * min (1 / Real.sqrt (lam P n X)) 1 * |(Y n m X i ((j : ℤ) - 1) ω : ℝ) + 1 - lam P n X|) ∂P
      ≤ prob P X i * prob P X j * (8 * m + 5 + 4 * Real.sqrt ((n : ℝ) * φ (m + 1)))
        + 8 * min (1 / Real.sqrt (lam P n X)) 1 * (n * prob P X i + lam P n X) * φ (m + 1) := by
  have hXm := hX.1; have hX1 := hX.2.2
  have hgood : ∀ᵐ ω ∂P, ∀ k, X k ω ≤ 1 := ae_all_iff.mpr hX1
  have hφ0 := phi_nonneg hφ (m + 1)
  obtain ⟨hc0, hcl, hln, -⟩ := EV_facts P n X hX m i j hij
  have hl0 : 0 ≤ lam P n X := hc0.trans hcl
  have hμ0 : 0 ≤ min (1 / Real.sqrt (lam P n X)) 1 := le_min (by positivity) zero_le_one
  have hG01 : ∀ᵐ ω ∂P, (X j ω : ℝ) = 0 ∨ (X j ω : ℝ) = 1 := by
    filter_upwards [hX1 j] with ω h2
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h2 with b | b <;> simp [b]
  have hYv : ∀ᵐ ω ∂P, Vij n m X i j ω ≤ Y n m X i ((j : ℤ) - 1) ω ∧
      Y n m X i ((j : ℤ) - 1) ω ≤ Vij n m X i j ω + 3 * m := by
    filter_upwards [hgood] with ω hx
    obtain ⟨b1, b2, b3⟩ := Y_bounds n m X i j (mem_Icc.mp hi).1 (mem_Icc.mp hj).1 hij ω hx
    exact ⟨b1.trans b2, b3⟩
  have h := core_YB P n X hX φ hφ m i j hi hj hij _ (Gsingle_meas X i j) hG01 _
    (meas_Y n m X hXm i _) hYv
  rw [int_X P X hXm hX1 j] at h
  have hpi0 : 0 ≤ prob P X i := measureReal_nonneg
  have hpi1 : prob P X i ≤ 1 := measureReal_le_one
  have hpj0 : 0 ≤ prob P X j := measureReal_nonneg
  have hpj1 : prob P X j ≤ 1 := measureReal_le_one
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm := mul_le_mul_of_nonneg_left h hpi0
  set μ := min (1 / Real.sqrt (lam P n X)) 1
  have k1 : prob P X i * (2 * μ * (4 * n * prob P X j * φ (m + 1) + φ (m + 1) * (2 * lam P n X)))
      ≤ 8 * μ * (n * prob P X i + lam P n X) * φ (m + 1) := by
    have a1 : prob P X i * prob P X j ≤ prob P X i := mul_le_of_le_one_right hpi0 hpj1
    have a2 : prob P X i * lam P n X ≤ lam P n X := mul_le_of_le_one_left hl0 hpi1
    have a3 : 0 ≤ μ * φ (m + 1) := mul_nonneg hμ0 hφ0
    have a4 : 0 ≤ μ * φ (m + 1) * n := mul_nonneg a3 hn0
    nlinarith [mul_le_mul_of_nonneg_left a1 a4, mul_le_mul_of_nonneg_left a2 a3]
  nlinarith

end PoissonDepTrials.MixInv

open PoissonDepTrials.MixInv


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ) (m : ℕ) (i j : ℕ)
    (hi : i ∈ Finset.Icc 1 n) (hj : j ∈ Finset.Icc 1 n) (hij : |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m) :
    prob P X i * ∫ ω, (X j ω : ℝ) *
        (1 + 2 * min (1 / Real.sqrt (lam P n X)) 1 * |(Y n m X i ((j : ℤ) - 1) ω : ℝ) + 1 - lam P n X|) ∂P
      ≤ prob P X i * prob P X j * (8 * m + 5 + 4 * Real.sqrt ((n : ℝ) * φ (m + 1)))
        + 8 * min (1 / Real.sqrt (lam P n X)) 1 * (n * prob P X i + lam P n X) * φ (m + 1) := by
  exact bound_4_19_core P n X hX φ hφ m i j hi hj hij

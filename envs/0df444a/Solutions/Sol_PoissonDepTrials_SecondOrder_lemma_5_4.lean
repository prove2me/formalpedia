-- Prove2me | solution 1 for PoissonDepTrials.SecondOrder.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:14:33.164984+00:00
-- url     : https://prove2.me/submissions/ba8cbee0-8915-4443-8cec-1849f713e5c8

import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

open MeasureTheory ProbabilityTheory Finset


namespace PoissonDepTrials.SecondOrder

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


lemma hasSum_of_eq' {f g : ℕ → ℝ} {a b : ℝ} (H : HasSum f a) (hf : ∀ k, f k = g k) (ha : a = b) :
    HasSum g b := by
  have : f = g := funext hf
  subst this; subst ha; exact H

lemma ps0 (b : ℝ) : HasSum (fun k : ℕ => b ^ k / (k.factorial : ℝ)) (Real.exp b) := by
  have := (Real.summable_pow_div_factorial b).hasSum
  rwa [exp_tsum'] at this

lemma ps1 (b : ℝ) : HasSum (fun k : ℕ => (k : ℝ) * (b ^ k / (k.factorial : ℝ))) (b * Real.exp b) := by
  rw [← hasSum_nat_add_iff' 1]
  refine hasSum_of_eq' ((ps0 b).mul_left b) (fun n => ?_) (by simp)
  rw [Nat.factorial_succ, pow_succ]; push_cast
  have : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

lemma ps2 (b : ℝ) : HasSum (fun k : ℕ => ((k : ℝ) * ((k : ℝ) - 1)) * (b ^ k / (k.factorial : ℝ)))
    (b ^ 2 * Real.exp b) := by
  rw [← hasSum_nat_add_iff' 2]
  refine hasSum_of_eq' ((ps0 b).mul_left (b ^ 2)) (fun n => ?_) (by simp [sum_range_succ])
  rw [show n + 2 = (n + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ, pow_succ, pow_succ]
  push_cast
  have : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma pois_mass (b : ℝ) : HasSum (fun k : ℕ => Real.exp (-b) * b ^ k / (k.factorial : ℝ)) 1 := by
  refine hasSum_of_eq' ((ps0 b).mul_left (Real.exp (-b))) (fun k => by ring) ?_
  rw [← Real.exp_add]; simp

lemma pois_var (b : ℝ) : HasSum (fun k : ℕ => Real.exp (-b) * b ^ k / (k.factorial : ℝ) * ((k : ℝ) - b) ^ 2) b := by
  have H := ((((ps2 b).add (ps1 b)).sub ((ps1 b).mul_left (2 * b))).add ((ps0 b).mul_left (b ^ 2))).mul_left
    (Real.exp (-b))
  refine hasSum_of_eq' H (fun k => by ring) ?_
  have : Real.exp (-b) * Real.exp b = 1 := by rw [← Real.exp_add]; simp
  linear_combination (b) * this

lemma abs_le_amgm (x s : ℝ) (hs : 0 < s) : |x| ≤ (x ^ 2 / s + s) / 2 := by
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2), div_add' _ _ _ hs.ne', le_div_iff₀ hs]
  have := sq_abs x
  nlinarith [sq_nonneg (|x| - s)]

theorem l53_core (lam : ℝ) (hlam : 0 < lam) (b : ℝ) (hb : 0 < b) (h : ℕ → ℝ) (M : ℝ)
    (hM : ∀ k, |h k| ≤ M) (m : ℕ) :
    poissonExp b (fun w => |stU lam h (w + m)|) ≤
      2 * lam⁻¹ * M * (1 + 2 * |(m : ℝ) + 1 + b - lam| + 2 * Real.sqrt b * min (1 / Real.sqrt lam) 1) := by
  set c := min (1 / Real.sqrt lam) 1 with hc
  set a := |(m : ℝ) + 1 + b - lam| with ha
  have hM0 := M_nonneg' h M hM
  have hc0 : 0 ≤ c := le_min (by positivity) zero_le_one
  have hc1 : c ≤ 1 := min_le_right _ _
  have hsb := Real.sqrt_pos.2 hb
  have hsbb : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb.le
  set p : ℕ → ℝ := fun k => Real.exp (-b) * b ^ k / (k.factorial : ℝ) with hp
  have hp0 : ∀ k, 0 ≤ p k := fun k => by simp only [hp]; positivity
  set A0 := lam⁻¹ * M * (2 + 4 * c * a + 2 * c * Real.sqrt b) with hA0
  set A1 := lam⁻¹ * M * (2 * c / Real.sqrt b) with hA1
  have hpt : ∀ k : ℕ, |stU lam h (k + m)| ≤ A0 + A1 * ((k : ℝ) - b) ^ 2 := by
    intro k
    have h1 := l35_core lam hlam h M hM (k + m + 1) (by omega)
    have e : stU lam h (k + m) = delta (stein lam h) (k + m + 1) := rfl
    rw [e]
    refine h1.trans ?_
    push_cast
    have h2 : |(k : ℝ) + m + 1 - lam| ≤ |(k:ℝ) - b| + a := by
      rw [ha]; calc |(k : ℝ) + m + 1 - lam| = |((k:ℝ) - b) + ((m : ℝ) + 1 + b - lam)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have h3 := abs_le_amgm ((k:ℝ) - b) (Real.sqrt b) hsb
    have hlM : 0 ≤ lam⁻¹ * M := by positivity
    have : 2 + 4 * |(k : ℝ) + m + 1 - lam| * c ≤
        (2 + 4 * c * a + 2 * c * Real.sqrt b) + (2 * c / Real.sqrt b) * ((k : ℝ) - b) ^ 2 := by
      have h4 : |(k : ℝ) + m + 1 - lam| * c ≤ (((k:ℝ) - b) ^ 2 / Real.sqrt b + Real.sqrt b) / 2 * c + a * c :=
        by nlinarith
      have : (2 * c / Real.sqrt b) * ((k : ℝ) - b) ^ 2 = 2 * c * (((k:ℝ) - b) ^ 2 / Real.sqrt b) := by ring
      nlinarith
    calc lam⁻¹ * M * (2 + 4 * |(k : ℝ) + m + 1 - lam| * c)
        ≤ lam⁻¹ * M * ((2 + 4 * c * a + 2 * c * Real.sqrt b) + (2 * c / Real.sqrt b) * ((k : ℝ) - b) ^ 2) :=
          mul_le_mul_of_nonneg_left this hlM
      _ = A0 + A1 * ((k : ℝ) - b) ^ 2 := by rw [hA0, hA1]; ring
  have HG : HasSum (fun k : ℕ => p k * (A0 + A1 * ((k : ℝ) - b) ^ 2)) (A0 + A1 * b) := by
    refine hasSum_of_eq' (((pois_mass b).mul_left A0).add ((pois_var b).mul_left A1))
      (fun k => by simp only [hp]; ring) (by ring)
  have hsumL : Summable (fun k : ℕ => p k * |stU lam h (k + m)|) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (hp0 k) (abs_nonneg _))
      (fun k => mul_le_mul_of_nonneg_left (hpt k) (hp0 k)) HG.summable
  have hle : poissonExp b (fun w => |stU lam h (w + m)|) ≤ A0 + A1 * b := by
    unfold poissonExp
    rw [← HG.tsum_eq]
    exact hsumL.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (hpt k) (hp0 k)) HG.summable
  refine hle.trans ?_
  have e2 : A1 * b = lam⁻¹ * M * (2 * c * Real.sqrt b) := by
    rw [hA1]; nth_rewrite 2 [← hsbb]; field_simp
  rw [e2, hA0]
  have hlM : 0 ≤ lam⁻¹ * M := by positivity
  have ha0 : 0 ≤ a := abs_nonneg _
  have : 4 * c * a ≤ 4 * a := by nlinarith
  calc lam⁻¹ * M * (2 + 4 * c * a + 2 * c * Real.sqrt b) + lam⁻¹ * M * (2 * c * Real.sqrt b)
      = lam⁻¹ * M * (2 + 4 * c * a + 4 * Real.sqrt b * c) := by ring
    _ ≤ lam⁻¹ * M * (2 + 4 * a + 4 * Real.sqrt b * c) := mul_le_mul_of_nonneg_left (by linarith) hlM
    _ = 2 * lam⁻¹ * M * (1 + 2 * a + 2 * Real.sqrt b * c) := by ring


lemma g_tsum_zero' (lam : ℝ) (f : ℕ → ℝ) (hs : Summable (fun k => lam ^ k / (k.factorial:ℝ) * f k)) :
    ∑' k, (f k - poissonExp lam f) * lam ^ k / (k.factorial : ℝ) = 0 := by
  have hs2 := (Real.summable_pow_div_factorial lam).mul_left (poissonExp lam f)
  have e : (fun k => (f k - poissonExp lam f) * lam ^ k / (k.factorial : ℝ)) =
      fun k => lam ^ k / (k.factorial:ℝ) * f k - poissonExp lam f * (lam ^ k / (k.factorial:ℝ)) := by
    funext k; ring
  rw [e, hs.tsum_sub hs2, tsum_mul_left, exp_tsum']
  have hP := pe_eq lam f
  have : ∑' k, lam ^ k / (k.factorial:ℝ) * f k = Real.exp lam * poissonExp lam f := by
    rw [hP, ← mul_assoc, ← Real.exp_add]; simp
  rw [this]; ring

lemma stein_tail' (lam : ℝ) (f : ℕ → ℝ) (hs : Summable (fun k => lam ^ k / (k.factorial:ℝ) * f k)) (w : ℕ) :
    ∑ k ∈ range w, (f k - poissonExp lam f) * lam ^ k / (k.factorial : ℝ) =
      -∑' k, (f (k + w) - poissonExp lam f) * lam ^ (k + w) / ((k + w).factorial : ℝ) := by
  have hs' : Summable (fun k => (f k - poissonExp lam f) * lam ^ k / (k.factorial : ℝ)) := by
    have hs2 := (Real.summable_pow_div_factorial lam).mul_left (poissonExp lam f)
    refine (hs.sub hs2).congr (fun k => ?_)
    ring
  have := hs'.sum_add_tsum_nat_add w
  rw [g_tsum_zero' lam f hs] at this
  linarith

lemma pe_comb3 (b : ℝ) (f f1 f2 f3 : ℕ → ℝ) (α1 α2 α3 : ℝ)
    (hf : ∀ j, f j = α1 * f1 j + α2 * f2 j + α3 * f3 j)
    (s1 : Summable (fun k => b ^ k / (k.factorial:ℝ) * f1 k))
    (s2 : Summable (fun k => b ^ k / (k.factorial:ℝ) * f2 k))
    (s3 : Summable (fun k => b ^ k / (k.factorial:ℝ) * f3 k)) :
    poissonExp b f = α1 * poissonExp b f1 + α2 * poissonExp b f2 + α3 * poissonExp b f3 := by
  rw [pe_eq, pe_eq, pe_eq, pe_eq]
  have e : (fun k => b ^ k / (k.factorial:ℝ) * f k) = fun k =>
      (α1 * (b ^ k / (k.factorial:ℝ) * f1 k) + α2 * (b ^ k / (k.factorial:ℝ) * f2 k)) +
        α3 * (b ^ k / (k.factorial:ℝ) * f3 k) := by
    funext k; rw [hf]; ring
  rw [e, Summable.tsum_add ((s1.mul_left α1).add (s2.mul_left α2)) (s3.mul_left α3),
    Summable.tsum_add (s1.mul_left α1) (s2.mul_left α2), tsum_mul_left, tsum_mul_left, tsum_mul_left]
  ring

lemma stein_comb3 (b : ℝ) (f f1 f2 f3 : ℕ → ℝ) (α1 α2 α3 : ℝ)
    (hf : ∀ j, f j = α1 * f1 j + α2 * f2 j + α3 * f3 j)
    (hP : poissonExp b f = α1 * poissonExp b f1 + α2 * poissonExp b f2 + α3 * poissonExp b f3) (w : ℕ) :
    stein b f w = α1 * stein b f1 w + α2 * stein b f2 w + α3 * stein b f3 w := by
  unfold stein
  have : ∀ j ∈ range w, (f j - poissonExp b f) * b ^ j / (j.factorial : ℝ) =
      α1 * ((f1 j - poissonExp b f1) * b ^ j / (j.factorial : ℝ)) +
      α2 * ((f2 j - poissonExp b f2) * b ^ j / (j.factorial : ℝ)) +
      α3 * ((f3 j - poissonExp b f3) * b ^ j / (j.factorial : ℝ)) := by
    intro j _; rw [hf, hP]; ring
  rw [sum_congr rfl this, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
  ring

lemma summ_lin (b : ℝ) (hb : 0 ≤ b) (f : ℕ → ℝ) (G : ℝ) (hf : ∀ k, |f k| ≤ G * ((k:ℝ) + b)) :
    Summable (fun k => b ^ k / (k.factorial:ℝ) * f k) := by
  have H := (((ps1 b).summable).mul_left G).add (((ps0 b).summable).mul_left (G * b))
  refine Summable.of_norm_bounded H (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast, abs_of_nonneg hb]
  have hq : 0 ≤ b ^ k / (k.factorial:ℝ) := by positivity
  calc b ^ k / (k.factorial:ℝ) * |f k| ≤ b ^ k / (k.factorial:ℝ) * (G * ((k:ℝ) + b)) :=
        mul_le_mul_of_nonneg_left (hf k) hq
    _ = _ := by ring

lemma headtel (b : ℝ) (hb : 0 < b) (n : ℕ) :
    ∑ j ∈ range (n + 1), (b - j) * (b ^ j / (j.factorial : ℝ)) = b * (b ^ n / (n.factorial : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, Nat.factorial_succ, pow_succ]
    push_cast
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring

lemma pe_abs_lin (b : ℝ) (hb : 0 < b) (g : ℕ → ℝ) (G : ℝ) (hg : ∀ j, |g j| ≤ G) :
    |poissonExp b (fun j => ((j:ℝ) - b) * g j)| ≤ G * Real.sqrt b := by
  have hsb := Real.sqrt_pos.2 hb
  have hsbb : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb.le
  have HG : HasSum (fun k : ℕ => Real.exp (-b) * b ^ k / (k.factorial : ℝ) *
      (G * ((((k:ℝ) - b) ^ 2 / Real.sqrt b + Real.sqrt b) / 2))) (G * Real.sqrt b) := by
    refine hasSum_of_eq' (((pois_var b).mul_left (G / (2 * Real.sqrt b))).add
      ((pois_mass b).mul_left (G * Real.sqrt b / 2))) (fun k => by field_simp; try ring) ?_
    have : b / (2 * Real.sqrt b) = Real.sqrt b / 2 := by
      rw [div_eq_div_iff (by positivity) (by norm_num)]; nlinarith [hsbb]
    calc G / (2 * Real.sqrt b) * b + G * Real.sqrt b / 2 * 1 = G * (b / (2 * Real.sqrt b)) + G * Real.sqrt b / 2 := by ring
      _ = _ := by rw [this]; ring
  unfold poissonExp
  rw [← Real.norm_eq_abs]
  refine tsum_of_norm_bounded HG (fun k => ?_)
  have hp : 0 ≤ Real.exp (-b) * b ^ k / (k.factorial : ℝ) := by positivity
  have hG0 : 0 ≤ G := (abs_nonneg _).trans (hg 0)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp, abs_mul]
  apply mul_le_mul_of_nonneg_left _ hp
  calc |(k:ℝ) - b| * |g k| ≤ ((((k:ℝ) - b) ^ 2 / Real.sqrt b + Real.sqrt b) / 2) * G :=
        mul_le_mul (abs_le_amgm _ _ hsb) (hg k) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem key3 (b : ℝ) (hb : 0 < b) (g : ℕ → ℝ) (G : ℝ) (hg : ∀ j, |g j| ≤ G) (w : ℕ) (hw : 1 ≤ w) :
    |stein b (fun j => ((j:ℝ) - b) * g j) w| ≤ 3 * G := by
  have hG0 : 0 ≤ G := (abs_nonneg _).trans (hg 0)
  set k : ℕ → ℝ := fun j => ((j:ℝ) - b) * g j with hk
  have hkb : ∀ j, |k j| ≤ G * ((j:ℝ) + b) := by
    intro j; simp only [hk]; rw [abs_mul]
    have : |(j:ℝ) - b| ≤ (j:ℝ) + b := by
      rw [abs_le]; constructor <;> nlinarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
    calc |(j:ℝ) - b| * |g j| ≤ ((j:ℝ) + b) * G :=
          mul_le_mul this (hg j) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hks := summ_lin b hb.le k G hkb
  set P := poissonExp b k with hPdef
  have hP : |P| ≤ G * Real.sqrt b := pe_abs_lin b hb g G hg
  obtain ⟨n, rfl⟩ : ∃ n, w = n + 1 := ⟨w - 1, by omega⟩
  have hC : (n.factorial : ℝ) * (b ^ (n+1))⁻¹ * (b * (b ^ n / (n.factorial : ℝ))) = 1 := by
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    have : b ^ n ≠ 0 := by positivity
    field_simp; ring
  have hC0 : (0:ℝ) ≤ (n.factorial : ℝ) * (b ^ (n+1))⁻¹ := by positivity
  have hsb := Real.sqrt_pos.2 hb
  unfold stein
  simp only [Nat.add_sub_cancel]
  rw [abs_neg, abs_mul, abs_of_nonneg hC0]
  rcases le_or_gt (((n + 1 : ℕ)) : ℝ) b with hwb | hwb
  · -- head
    have hA := l31_core b (n+1) hw hwb
    have hsplit : ∑ j ∈ range (n+1), (k j - P) * b ^ j / (j.factorial : ℝ) =
        ∑ j ∈ range (n+1), k j * (b ^ j / (j.factorial : ℝ)) - P * ∑ j ∈ range (n+1), b ^ j / (j.factorial : ℝ) := by
      rw [mul_sum, ← sum_sub_distrib]; apply sum_congr rfl; intro j _; ring
    have h1 : |∑ j ∈ range (n+1), k j * (b ^ j / (j.factorial : ℝ))| ≤ G * (b * (b ^ n / (n.factorial : ℝ))) := by
      rw [← headtel b hb n, mul_sum]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun j hj => ?_))
      have hj : (j:ℝ) ≤ b := by
        have : j < n + 1 := mem_range.mp hj
        have : (j:ℝ) + 1 ≤ ((n+1 : ℕ):ℝ) := by exact_mod_cast this
        linarith
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ b ^ j / (j.factorial : ℝ))]
      simp only [hk]
      rw [abs_mul, abs_of_nonpos (by linarith : (j:ℝ) - b ≤ 0)]
      have := hg j
      have hq : (0:ℝ) ≤ b ^ j / (j.factorial : ℝ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this (by linarith : (0:ℝ) ≤ b - j)]
    rw [hsplit]
    have h2 := abs_sub (∑ j ∈ range (n+1), k j * (b ^ j / (j.factorial : ℝ)))
      (P * ∑ j ∈ range (n+1), b ^ j / (j.factorial : ℝ))
    rw [abs_mul (P), abs_of_nonneg (by positivity : (0:ℝ) ≤ ∑ j ∈ range (n+1), b ^ j / (j.factorial : ℝ))] at h2
    set C := (n.factorial : ℝ) * (b ^ (n+1))⁻¹
    have hA' : C * ∑ j ∈ range (n+1), b ^ j / (j.factorial : ℝ) ≤ 2 / Real.sqrt b := by
      simpa using hA
    calc C * |∑ j ∈ range (n+1), k j * (b ^ j / (j.factorial : ℝ)) - P * ∑ j ∈ range (n+1), b ^ j / (j.factorial : ℝ)|
        ≤ C * (G * (b * (b ^ n / (n.factorial : ℝ))) + |P| * ∑ j ∈ range (n+1), b ^ j / (j.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) hC0
      _ = G * (C * (b * (b ^ n / (n.factorial : ℝ)))) + |P| * (C * ∑ j ∈ range (n+1), b ^ j / (j.factorial : ℝ)) := by ring
      _ ≤ G * 1 + (G * Real.sqrt b) * (2 / Real.sqrt b) := by
          rw [hC]; gcongr
      _ = 3 * G := by field_simp; ring
  · -- tail
    have hB := l32_core b hb (n+1) hw hwb.le
    rw [stein_tail' b k hks (n+1), abs_neg]
    set C := (n.factorial : ℝ) * (b ^ (n+1))⁻¹
    set T := ∑' i : ℕ, b ^ (i + (n+1)) / ((i + (n+1)).factorial : ℝ) with hT
    have hB' : C * T ≤ 2 / Real.sqrt ((n+1 : ℕ) : ℝ) := by simpa using hB
    -- HasSum of the tail of (j - b) q_j
    have H1 : HasSum (fun i : ℕ => ((i + (n+1) : ℕ) : ℝ) * (b ^ (i + (n+1)) / ((i + (n+1)).factorial : ℝ)))
        (b * Real.exp b - ∑ j ∈ range (n+1), (j:ℝ) * (b ^ j / (j.factorial : ℝ))) :=
      (hasSum_nat_add_iff' (n+1)).mpr (ps1 b)
    have H0 : HasSum (fun i : ℕ => b ^ (i + (n+1)) / ((i + (n+1)).factorial : ℝ))
        (Real.exp b - ∑ j ∈ range (n+1), b ^ j / (j.factorial : ℝ)) :=
      (hasSum_nat_add_iff' (n+1)).mpr (ps0 b)
    have hTeq : T = Real.exp b - ∑ j ∈ range (n+1), b ^ j / (j.factorial : ℝ) := H0.tsum_eq
    have Htail : HasSum (fun i : ℕ => (((i + (n+1) : ℕ) : ℝ) - b) * (b ^ (i + (n+1)) / ((i + (n+1)).factorial : ℝ)))
        (b * (b ^ n / (n.factorial : ℝ))) := by
      refine hasSum_of_eq' (H1.sub (H0.mul_left b)) (fun i => by ring) ?_
      rw [← headtel b hb n]
      rw [show ∑ x ∈ range (n+1), (b - (x:ℝ)) * (b ^ x / (x.factorial : ℝ)) =
          b * ∑ x ∈ range (n+1), b ^ x / (x.factorial : ℝ) - ∑ x ∈ range (n+1), (x:ℝ) * (b ^ x / (x.factorial : ℝ)) by
        rw [mul_sum, ← sum_sub_distrib]; apply sum_congr rfl; intro x _; ring]
      ring
    have HB : HasSum (fun i : ℕ => G * ((((i + (n+1) : ℕ) : ℝ) - b) * (b ^ (i + (n+1)) / ((i + (n+1)).factorial : ℝ)))
        + |P| * (b ^ (i + (n+1)) / ((i + (n+1)).factorial : ℝ)))
        (G * (b * (b ^ n / (n.factorial : ℝ))) + |P| * T) := by
      rw [hTeq]; exact (Htail.mul_left G).add (H0.mul_left |P|)
    have hb2 : |∑' i, (k (i + (n+1)) - P) * b ^ (i + (n+1)) / ((i + (n+1)).factorial : ℝ)| ≤
        G * (b * (b ^ n / (n.factorial : ℝ))) + |P| * T := by
      rw [← Real.norm_eq_abs]
      refine tsum_of_norm_bounded HB (fun i => ?_)
      have hq : (0:ℝ) ≤ b ^ (i + (n+1)) / ((i + (n+1)).factorial : ℝ) := by positivity
      have hib : b ≤ ((i + (n+1) : ℕ) : ℝ) := by
        have : ((n+1 : ℕ) : ℝ) ≤ ((i + (n+1) : ℕ) : ℝ) := by exact_mod_cast (by omega : n + 1 ≤ i + (n+1))
        linarith
      rw [Real.norm_eq_abs, mul_div_assoc, abs_mul, abs_of_nonneg hq]
      have h3 : |k (i + (n+1)) - P| ≤ G * (((i + (n+1) : ℕ) : ℝ) - b) + |P| := by
        refine (abs_sub _ _).trans ?_
        simp only [hk]
        rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ ((i + (n+1) : ℕ) : ℝ) - b)]
        have := hg (i + (n+1))
        nlinarith [mul_le_mul_of_nonneg_left this (by linarith : (0:ℝ) ≤ ((i + (n+1) : ℕ) : ℝ) - b)]
      calc |k (i + (n+1)) - P| * (b ^ (i + (n+1)) / ((i + (n+1)).factorial : ℝ))
          ≤ (G * (((i + (n+1) : ℕ) : ℝ) - b) + |P|) * (b ^ (i + (n+1)) / ((i + (n+1)).factorial : ℝ)) :=
            mul_le_mul_of_nonneg_right h3 hq
        _ = _ := by ring
    have hsw : Real.sqrt b ≤ Real.sqrt ((n+1 : ℕ) : ℝ) := Real.sqrt_le_sqrt hwb.le
    have hsw0 : 0 < Real.sqrt ((n+1 : ℕ) : ℝ) := lt_of_lt_of_le hsb hsw
    calc C * |∑' i, (k (i + (n+1)) - P) * b ^ (i + (n+1)) / ((i + (n+1)).factorial : ℝ)|
        ≤ C * (G * (b * (b ^ n / (n.factorial : ℝ))) + |P| * T) := mul_le_mul_of_nonneg_left hb2 hC0
      _ = G * (C * (b * (b ^ n / (n.factorial : ℝ)))) + |P| * (C * T) := by ring
      _ ≤ G * 1 + (G * Real.sqrt b) * (2 / Real.sqrt ((n+1 : ℕ) : ℝ)) := by
          rw [hC]; gcongr
      _ ≤ G * 1 + (G * Real.sqrt ((n+1 : ℕ) : ℝ)) * (2 / Real.sqrt ((n+1 : ℕ) : ℝ)) := by gcongr
      _ = 3 * G := by field_simp; ring

theorem l54_core (lam : ℝ) (hlam : 0 < lam) (b : ℝ) (hb : 0 < b) (h : ℕ → ℝ) (M : ℝ)
    (hM : ∀ k, |h k| ≤ M) :
    ∀ w : ℕ, 1 ≤ w → |stein b (stU lam h) w| ≤
      4 * lam⁻¹ * M * ((2 + 4 * |1 + b - lam|) * min (1 / Real.sqrt b) 1 +
        3 * min (1 / Real.sqrt lam) 1) := by
  intro w hw
  set cl := min (1 / Real.sqrt lam) 1 with hcl
  set cb := min (1 / Real.sqrt b) 1 with hcb
  have hM0 := M_nonneg' h M hM
  have hcl0 : 0 ≤ cl := le_min (by positivity) zero_le_one
  have hcl1 : cl ≤ 1 := min_le_right _ _
  have hcb0 : 0 ≤ cb := le_min (by positivity) zero_le_one
  have hPl := pe_abs_le lam hlam.le h M hM
  set g1 : ℕ → ℝ := fun j => h (j + 1) - poissonExp lam h with hg1
  set g2 : ℕ → ℝ := fun j => stein lam h (j + 1) with hg2
  set g3 : ℕ → ℝ := fun j => ((j:ℝ) - b) * g2 j with hg3
  have hb1 : ∀ j, |g1 j| ≤ 2 * M := fun j => by
    simp only [hg1]
    have := hM (j+1)
    calc |h (j+1) - poissonExp lam h| ≤ |h (j+1)| + |poissonExp lam h| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  have hb2 : ∀ j, |g2 j| ≤ 4 * M * cl := fun j => l33_core lam hlam h M hM (j + 1) (by omega)
  have hb3 : ∀ j, |g3 j| ≤ 4 * M * cl * ((j:ℝ) + b) := by
    intro j; simp only [hg3]; rw [abs_mul]
    have : |(j:ℝ) - b| ≤ (j:ℝ) + b := by
      rw [abs_le]; constructor <;> nlinarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
    calc |(j:ℝ) - b| * |g2 j| ≤ ((j:ℝ) + b) * (4 * M * cl) :=
          mul_le_mul this (hb2 j) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hU : ∀ j, stU lam h j = (-lam⁻¹) * g1 j + (lam⁻¹ * (1 + b - lam)) * g2 j + lam⁻¹ * g3 j := by
    intro j
    have hE := stein_eq lam hlam h (j + 1)
    simp only [stU, delta, hg1, hg2, hg3]
    push_cast at hE
    field_simp
    linarith
  have s1 := summ_bdd b g1 (2 * M) hb1
  have s2 := summ_bdd b g2 (4 * M * cl) hb2
  have s3 := summ_lin b hb.le g3 (4 * M * cl) hb3
  have hP := pe_comb3 b (stU lam h) g1 g2 g3 _ _ _ hU s1 s2 s3
  rw [stein_comb3 b (stU lam h) g1 g2 g3 _ _ _ hU hP w]
  have e1 := l33_core b hb g1 (2 * M) hb1 w hw
  have e2 := l33_core b hb g2 (4 * M * cl) hb2 w hw
  have e3 := key3 b hb g2 (4 * M * cl) hb2 w hw
  have hli : 0 < lam⁻¹ := inv_pos.2 hlam
  have t1 : |(-lam⁻¹) * stein b g1 w| ≤ lam⁻¹ * (4 * (2 * M) * cb) := by
    rw [abs_mul, abs_neg, abs_of_pos hli]; exact mul_le_mul_of_nonneg_left e1 hli.le
  have t2 : |(lam⁻¹ * (1 + b - lam)) * stein b g2 w| ≤ lam⁻¹ * (|1 + b - lam| * (4 * (4 * M * cl) * cb)) := by
    rw [abs_mul, abs_mul, abs_of_pos hli, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e2 (abs_nonneg _)) hli.le
  have t3 : |lam⁻¹ * stein b g3 w| ≤ lam⁻¹ * (3 * (4 * M * cl)) := by
    rw [abs_mul, abs_of_pos hli]; exact mul_le_mul_of_nonneg_left e3 hli.le
  have tri := abs_add_three ((-lam⁻¹) * stein b g1 w) ((lam⁻¹ * (1 + b - lam)) * stein b g2 w) (lam⁻¹ * stein b g3 w)
  have hcc : |1 + b - lam| * (4 * (4 * M * cl) * cb) ≤ |1 + b - lam| * (16 * M * cb) := by
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have : M * cl * cb ≤ M * cb := by
      have := mul_le_mul_of_nonneg_left hcl1 (mul_nonneg hM0 hcb0)
      nlinarith
    nlinarith
  have t2' : |(lam⁻¹ * (1 + b - lam)) * stein b g2 w| ≤ lam⁻¹ * (|1 + b - lam| * (16 * M * cb)) :=
    t2.trans (mul_le_mul_of_nonneg_left hcc hli.le)
  calc _ ≤ _ := tri
    _ ≤ lam⁻¹ * (4 * (2 * M) * cb) + lam⁻¹ * (|1 + b - lam| * (16 * M * cb)) + lam⁻¹ * (3 * (4 * M * cl)) := by
        linarith
    _ = 4 * lam⁻¹ * M * ((2 + 4 * |1 + b - lam|) * cb + 3 * cl) := by ring

end PoissonDepTrials.SecondOrder

open PoissonDepTrials.SecondOrder


theorem solution (lam : ℝ) (hlam : 0 < lam) (b : ℝ) (hb : 0 < b) (h : ℕ → ℝ) (M : ℝ)
    (hM : ∀ k, |h k| ≤ M) :
    ∀ w : ℕ, 1 ≤ w → |stein b (stU lam h) w| ≤
      4 * lam⁻¹ * M * ((2 + 4 * |1 + b - lam|) * min (1 / Real.sqrt b) 1 +
        3 * min (1 / Real.sqrt lam) 1) := by
  exact l54_core lam hlam b hb h M hM

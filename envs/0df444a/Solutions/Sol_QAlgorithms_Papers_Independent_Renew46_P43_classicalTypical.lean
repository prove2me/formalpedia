-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P43.classicalTypical
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T20:21:02.762258+00:00
-- url     : https://prove2.me/submissions/43c4d1ab-0776-496e-8e79-241f6e46df88

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

open scoped BigOperators

open QAlgorithms.Papers.Independent.Renew46.P43
open QAlgorithms.Papers.Independent.Dependency50.P19 (count)

namespace X6TCT

variable {I : Type} [Fintype I] [DecidableEq I]

/-- expectation of a single coordinate under the product law. -/
lemma exp_one (p : I → ℝ) (hp : ∑ j, p j = 1) {n : ℕ} (k : Fin n) (a : I → ℝ) :
    ∑ w : Fin n → I, (∏ m, p (w m)) * a (w k) = ∑ j, p j * a j := by
  have h := (Fintype.prod_sum (fun (m : Fin n) (j : I) => p j * (if m = k then a j else 1))).symm
  have e1 : ∀ w : Fin n → I, ∏ m, p (w m) * (if m = k then a (w m) else 1) =
      (∏ m, p (w m)) * a (w k) := by
    intro w
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k (fun m => a (w m))]
    simp
  simp only [e1] at h
  rw [h]
  have e2 : ∀ m, ∑ j, p j * (if m = k then a j else 1) = if m = k then ∑ j, p j * a j else 1 := by
    intro m; split_ifs <;> simp [hp]
  simp only [e2]
  rw [Finset.prod_ite_eq' Finset.univ k (fun _ => ∑ j, p j * a j)]
  simp

/-- expectation of a product of two distinct coordinates. -/
lemma exp_two (p : I → ℝ) (hp : ∑ j, p j = 1) {n : ℕ} (k l : Fin n) (hkl : k ≠ l)
    (a b : I → ℝ) :
    ∑ w : Fin n → I, (∏ m, p (w m)) * (a (w k) * b (w l)) =
      (∑ j, p j * a j) * ∑ j, p j * b j := by
  have h := (Fintype.prod_sum (fun (m : Fin n) (j : I) =>
    p j * ((if m = k then a j else 1) * (if m = l then b j else 1)))).symm
  have e1 : ∀ w : Fin n → I, ∏ m, p (w m) * ((if m = k then a (w m) else 1) *
      (if m = l then b (w m) else 1)) = (∏ m, p (w m)) * (a (w k) * b (w l)) := by
    intro w
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_ite_eq' Finset.univ k (fun m => a (w m)),
      Finset.prod_ite_eq' Finset.univ l (fun m => b (w m))]
    simp
  simp only [e1] at h
  rw [h]
  have e2 : ∀ m, ∑ j, p j * ((if m = k then a j else 1) * (if m = l then b j else 1)) =
      (if m = k then ∑ j, p j * a j else 1) * (if m = l then ∑ j, p j * b j else 1) := by
    intro m
    by_cases h1 : m = k
    · have h2 : m ≠ l := h1 ▸ hkl
      simp [h1, hkl]
    · by_cases h2 : m = l
      · subst h2; simp [h1, Ne.symm hkl]
      · simp [h1, h2, hp]
  simp only [e2]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k (fun _ => ∑ j, p j * a j),
    Finset.prod_ite_eq' Finset.univ l (fun _ => ∑ j, p j * b j)]
  simp

lemma count_eq {n : ℕ} (w : Fin n → I) (i : I) :
    (count w i : ℝ) = ∑ k, (if w k = i then (1 : ℝ) else 0) := by
  unfold count
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- the variance of a letter count. -/
lemma variance (p : I → ℝ) (hp : ∑ j, p j = 1) (n : ℕ) (i : I) :
    ∑ w : Fin n → I, (∏ m, p (w m)) * ((count w i : ℝ) - n * p i) ^ 2 =
      n * (p i * (1 - p i)) := by
  set g : I → ℝ := fun j => (if j = i then 1 else 0) - p i
  have hg : ∀ w : Fin n → I, (count w i : ℝ) - n * p i = ∑ k, g (w k) := by
    intro w
    rw [count_eq]; simp only [g, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hg0 : ∑ j, p j * g j = 0 := by
    simp only [g, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.sum_mul, hp, one_mul, sub_self]
  have hg2 : ∑ j, p j * g j ^ 2 = p i * (1 - p i) := by
    have : ∀ j, p j * g j ^ 2 =
        (if j = i then p i * ((1 - p i) ^ 2 - p i ^ 2) else 0) + p j * p i ^ 2 := by
      intro j; simp only [g]; split_ifs with h
      · subst h; ring
      · ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      ← Finset.sum_mul, hp]
    ring
  have key : ∀ k : Fin n, ∑ l : Fin n, ∑ w : Fin n → I, (∏ m, p (w m)) * (g (w k) * g (w l)) =
      p i * (1 - p i) := by
    intro k
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    have h1 : ∑ w : Fin n → I, (∏ m, p (w m)) * (g (w k) * g (w k)) = p i * (1 - p i) := by
      rw [← hg2]
      have := exp_one p hp k (fun j => g j * g j)
      simp only [sq]; exact this
    have h2 : ∑ l ∈ Finset.univ.erase k,
        ∑ w : Fin n → I, (∏ m, p (w m)) * (g (w k) * g (w l)) = 0 := by
      refine Finset.sum_eq_zero fun l hl => ?_
      rw [exp_two p hp k l (Finset.ne_of_mem_erase hl).symm g g, hg0, zero_mul]
    rw [h1, h2, add_zero]
  calc ∑ w : Fin n → I, (∏ m, p (w m)) * ((count w i : ℝ) - n * p i) ^ 2
      = ∑ k : Fin n, ∑ l : Fin n, ∑ w : Fin n → I, (∏ m, p (w m)) * (g (w k) * g (w l)) := by
        have e : ∀ w : Fin n → I, (∏ m, p (w m)) * ((count w i : ℝ) - n * p i) ^ 2 =
            ∑ k : Fin n, ∑ l : Fin n, (∏ m, p (w m)) * (g (w k) * g (w l)) := by
          intro w; rw [hg, sq, Finset.sum_mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
        simp only [e]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = n * (p i * (1 - p i)) := by
        simp only [key, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma total (p : I → ℝ) (hp : ∑ j, p j = 1) (n : ℕ) :
    ∑ w : Fin n → I, ∏ m, p (w m) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : Fin n) (j : I) => p j)]; simp [hp]

lemma W_nonneg (p : I → ℝ) (hp0 : ∀ j, 0 ≤ p j) {n : ℕ} (w : Fin n → I) :
    0 ≤ ∏ m, p (w m) := Finset.prod_nonneg fun m _ => hp0 _

/-- Chebyshev for one letter. -/
lemma bad (p : I → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp : ∑ j, p j = 1) (n : ℕ) (hn : 0 < n)
    (alpha : ℝ) (halpha : 0 < alpha) (i : I) :
    ∑ w ∈ Finset.univ.filter (fun w : Fin n → I => alpha * Real.sqrt (p i * (1 - p i)) *
      Real.sqrt n < |(count w i : ℝ) - n * p i|), ∏ m, p (w m) ≤ 1 / alpha ^ 2 := by
  set v := p i * (1 - p i)
  have hv := variance p hp n i
  have hpi1 : p i ≤ 1 := by
    rw [← hp]; exact Finset.single_le_sum (fun j _ => hp0 j) (Finset.mem_univ i)
  have hv0 : 0 ≤ v := mul_nonneg (hp0 i) (by linarith)
  set F := Finset.univ.filter (fun w : Fin n → I => alpha * Real.sqrt v *
      Real.sqrt n < |(count w i : ℝ) - n * p i|)
  have hterm : ∀ w : Fin n → I, 0 ≤ (∏ m, p (w m)) * ((count w i : ℝ) - n * p i) ^ 2 :=
    fun w => mul_nonneg (W_nonneg p hp0 w) (sq_nonneg _)
  have hsub : ∑ w ∈ F, (∏ m, p (w m)) * ((count w i : ℝ) - n * p i) ^ 2 ≤ n * v := by
    rw [← hv]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun w _ _ => hterm w)
  rcases hv0.lt_or_eq with hvpos | hvz
  · have ht2 : (alpha * Real.sqrt v * Real.sqrt n) ^ 2 = alpha ^ 2 * (n * v) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hv0, Real.sq_sqrt (Nat.cast_nonneg n)]; ring
    have hlow : (∑ w ∈ F, ∏ m, p (w m)) * (alpha ^ 2 * (n * v)) ≤
        ∑ w ∈ F, (∏ m, p (w m)) * ((count w i : ℝ) - n * p i) ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun w hw => ?_
      rw [Finset.mem_filter] at hw
      refine mul_le_mul_of_nonneg_left ?_ (W_nonneg p hp0 w)
      rw [← ht2, ← sq_abs ((count w i : ℝ) - n * p i)]
      have h0 : 0 ≤ alpha * Real.sqrt v * Real.sqrt n := by positivity
      nlinarith [hw.2]
    have hnv : 0 < n * v := mul_pos (by exact_mod_cast hn) hvpos
    rw [le_div_iff₀ (by positivity)]
    have := hlow.trans hsub
    have h2 : (∑ w ∈ F, ∏ m, p (w m)) * alpha ^ 2 * (n * v) ≤ 1 * (n * v) := by
      rw [mul_assoc]; linarith
    exact le_of_mul_le_mul_right h2 hnv
  · have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => hterm w)).mp
      (by rw [hv]; change (n : ℝ) * v = 0; rw [← hvz, mul_zero])
    have : ∑ w ∈ F, ∏ m, p (w m) = 0 := by
      refine Finset.sum_eq_zero fun w hw => ?_
      rw [Finset.mem_filter] at hw
      have h1 := hall w (Finset.mem_univ w)
      have h2 : 0 < ((count w i : ℝ) - n * p i) ^ 2 := by
        rw [← sq_abs]; have := hw.2; rw [← hvz] at this; simp at this; positivity
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · linarith
    rw [this]; positivity

/-- mass of the typical set. -/
lemma mass (p : I → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp : ∑ j, p j = 1) (n : ℕ) (hn : 0 < n)
    (alpha : ℝ) (halpha : 0 < alpha) :
    1 - Fintype.card I / alpha ^ 2 ≤
      ∑ w ∈ Finset.univ.filter (fun w : Fin n → I => ∀ i, |(count w i : ℝ) - n * p i| ≤
        alpha * Real.sqrt (p i * (1 - p i)) * Real.sqrt n), ∏ m, p (w m) := by
  set S := Finset.univ.filter (fun w : Fin n → I => ∀ i, |(count w i : ℝ) - n * p i| ≤
        alpha * Real.sqrt (p i * (1 - p i)) * Real.sqrt n)
  set B : I → Finset (Fin n → I) := fun i => Finset.univ.filter (fun w : Fin n → I =>
    alpha * Real.sqrt (p i * (1 - p i)) * Real.sqrt n < |(count w i : ℝ) - n * p i|)
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun w : Fin n → I => ∀ i, |(count w i : ℝ) - n * p i| ≤
        alpha * Real.sqrt (p i * (1 - p i)) * Real.sqrt n) (fun w => ∏ m, p (w m))
  rw [total p hp] at hsplit
  have hnot : ∑ w ∈ Finset.univ.filter (fun w : Fin n → I => ¬ ∀ i, |(count w i : ℝ) - n * p i| ≤
        alpha * Real.sqrt (p i * (1 - p i)) * Real.sqrt n), ∏ m, p (w m) ≤
      ∑ i, ∑ w ∈ B i, ∏ m, p (w m) := by
    calc _ ≤ ∑ w ∈ Finset.univ.filter (fun w : Fin n → I => ¬ ∀ i, |(count w i : ℝ) - n * p i| ≤
          alpha * Real.sqrt (p i * (1 - p i)) * Real.sqrt n),
          ∑ i, (if w ∈ B i then ∏ m, p (w m) else 0) := by
          refine Finset.sum_le_sum fun w hw => ?_
          rw [Finset.mem_filter] at hw
          push Not at hw
          obtain ⟨i, hi⟩ := hw.2
          have : (if w ∈ B i then ∏ m, p (w m) else 0) = ∏ m, p (w m) := by
            rw [if_pos]; simp [B, hi]
          calc ∏ m, p (w m) = (if w ∈ B i then ∏ m, p (w m) else 0) := this.symm
            _ ≤ _ := Finset.single_le_sum (f := fun i => if w ∈ B i then ∏ m, p (w m) else 0)
              (fun j _ => by split_ifs; exact W_nonneg p hp0 w; exact le_refl _) (Finset.mem_univ i)
      _ ≤ ∑ w : Fin n → I, ∑ i, (if w ∈ B i then ∏ m, p (w m) else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun w _ _ =>
            Finset.sum_nonneg fun j _ => by split_ifs; exact W_nonneg p hp0 w; exact le_refl _)
      _ = ∑ i, ∑ w ∈ B i, ∏ m, p (w m) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_ite_mem]; simp
  have hB : ∑ i, ∑ w ∈ B i, ∏ m, p (w m) ≤ Fintype.card I * (1 / alpha ^ 2) := by
    calc _ ≤ ∑ _i : I, 1 / alpha ^ 2 := Finset.sum_le_sum fun i _ => bad p hp0 hp n hn alpha halpha i
      _ = _ := by simp
  have : (Fintype.card I : ℝ) / alpha ^ 2 = Fintype.card I * (1 / alpha ^ 2) := by ring
  linarith

lemma sqrt_log {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.sqrt x * (-Real.log x) ≤ 2 / Real.exp 1 := by
  rcases h0.lt_or_eq with hx | hx
  · set s := Real.sqrt x
    have hs : 0 < s := Real.sqrt_pos.mpr hx
    have hlx : Real.log x = 2 * Real.log s := by
      rw [← Real.log_rpow hs, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        Real.sq_sqrt h0]
    have he := Real.exp_pos 1
    have key := Real.log_le_sub_one_of_pos (show 0 < 1 / (Real.exp 1 * s) by positivity)
    rw [Real.log_div (by norm_num) (by positivity), Real.log_one, Real.log_mul (by positivity)
      (by positivity), Real.log_exp] at key
    rw [hlx]
    have : -Real.log s ≤ 1 / (Real.exp 1 * s) := by linarith
    have h2 : s * (-Real.log s) ≤ s * (1 / (Real.exp 1 * s)) := mul_le_mul_of_nonneg_left this hs.le
    rw [show s * (1 / (Real.exp 1 * s)) = 1 / Real.exp 1 by field_simp] at h2
    have : s * -(2 * Real.log s) = 2 * (s * (-Real.log s)) := by ring
    rw [this, show 2 / Real.exp 1 = 2 * (1 / Real.exp 1) by ring]
    linarith
  · subst hx; simp; positivity

lemma card_le (p : I → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp : ∑ j, p j = 1) (n : ℕ)
    (alpha : ℝ) (halpha : 0 < alpha) :
    ((Finset.univ.filter (fun w : Fin n → I => ∀ i, |(count w i : ℝ) - n * p i| ≤
        alpha * Real.sqrt (p i * (1 - p i)) * Real.sqrt n)).card : ℝ) ≤
      Real.exp (n * (-∑ i, p i * Real.log (p i)) +
        alpha * Real.sqrt n * Fintype.card I * (2 / Real.exp 1)) := by
  set S := Finset.univ.filter (fun w : Fin n → I => ∀ i, |(count w i : ℝ) - n * p i| ≤
        alpha * Real.sqrt (p i * (1 - p i)) * Real.sqrt n)
  set X := n * (-∑ i, p i * Real.log (p i)) + alpha * Real.sqrt n * Fintype.card I * (2 / Real.exp 1)
  have hp1 : ∀ i, p i ≤ 1 := fun i => by
    rw [← hp]; exact Finset.single_le_sum (fun j _ => hp0 j) (Finset.mem_univ i)
  have hW : ∀ w ∈ S, Real.exp (-X) ≤ ∏ m, p (w m) := by
    intro w hw
    rw [Finset.mem_filter] at hw
    have hc := hw.2
    have hpos : ∀ k, 0 < p (w k) := by
      intro k
      by_contra hk
      have hz : p (w k) = 0 := le_antisymm (not_lt.mp hk) (hp0 _)
      have := hc (w k)
      rw [hz] at this; simp at this
      have h1 : 1 ≤ count w (w k) := by
        unfold count; exact Finset.card_pos.mpr ⟨k, by simp⟩
      omega
    have hWpos : 0 < ∏ m, p (w m) := Finset.prod_pos fun m _ => hpos m
    rw [← Real.exp_log hWpos, Real.exp_le_exp, Real.log_prod (fun m _ => (hpos m).ne')]
    have hfib : ∑ k, Real.log (p (w k)) = ∑ i, (count w i : ℝ) * Real.log (p i) := by
      rw [← Finset.sum_fiberwise Finset.univ w (fun k => Real.log (p (w k)))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_congr rfl (g := fun _ => Real.log (p i)) (fun k hk => by
        rw [(Finset.mem_filter.mp hk).2]), Finset.sum_const, nsmul_eq_mul]
      rfl
    rw [hfib]
    have hterm : ∀ i, (count w i : ℝ) * (-Real.log (p i)) ≤
        n * (-(p i * Real.log (p i))) + alpha * Real.sqrt n * (2 / Real.exp 1) := by
      intro i
      have hl : 0 ≤ -Real.log (p i) := by
        have := Real.log_nonpos (hp0 i) (hp1 i); linarith
      have hci : (count w i : ℝ) ≤ n * p i + alpha * Real.sqrt (p i * (1 - p i)) * Real.sqrt n :=
        by have := (abs_le.mp (hc i)).2; linarith
      have hsq : Real.sqrt (p i * (1 - p i)) * (-Real.log (p i)) ≤ 2 / Real.exp 1 := by
        refine le_trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) hl)
          (sqrt_log (hp0 i) (hp1 i))
        nlinarith [hp0 i, hp1 i]
      have h1 := mul_le_mul_of_nonneg_right hci hl
      have h2 : 0 ≤ alpha * Real.sqrt n := by positivity
      have h3 := mul_le_mul_of_nonneg_left hsq h2
      nlinarith
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum] at hsum
    simp only [X, Finset.sum_neg_distrib, mul_neg] at hsum ⊢
    have : ∑ i, (count w i : ℝ) * Real.log (p i) = -∑ i, (count w i : ℝ) * (-Real.log (p i)) := by
      simp [Finset.sum_neg_distrib]
    rw [this]; nlinarith
  have hmass : (S.card : ℝ) * Real.exp (-X) ≤ 1 := by
    calc (S.card : ℝ) * Real.exp (-X) = ∑ w ∈ S, Real.exp (-X) := by simp
      _ ≤ ∑ w ∈ S, ∏ m, p (w m) := Finset.sum_le_sum hW
      _ ≤ ∑ w : Fin n → I, ∏ m, p (w m) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun w _ _ => W_nonneg p hp0 w)
      _ = 1 := total p hp n
  rw [Real.exp_neg] at hmass
  have := Real.exp_pos X
  rwa [mul_inv_le_iff₀ this, one_mul] at hmass

end X6TCT

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : PMF I) (n : ℕ) (hn : 0 < n) (alpha : ℝ) (halpha : 0 < alpha) :
    (∑ w ∈ varianceSet P n alpha, ∏ k, (P (w k)).toReal) ≥
      1 - Fintype.card I / alpha^2 ∧
    ((varianceSet P n alpha).card : ℝ) ≤
      exp2 (n * pmfEntropy P + varianceConstant * Fintype.card I * alpha * Real.sqrt n) := by
  set p : I → ℝ := fun i => (P i).toReal
  have hp0 : ∀ j, 0 ≤ p j := fun j => ENNReal.toReal_nonneg
  have hp : ∑ j, p j = 1 := by
    have h1 : ∑ j, P j = 1 := by simpa using P.tsum_coe
    simp only [p]
    rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top P a), h1]
    simp
  refine ⟨X6TCT.mass p hp0 hp n hn alpha halpha, ?_⟩
  refine le_of_le_of_eq (X6TCT.card_le p hp0 hp n alpha halpha) ?_
  unfold exp2 pmfEntropy shannon varianceConstant
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  have hl : Real.log 2 ≠ 0 := by positivity
  have hH : -∑ i, (P i).toReal * Real.logb 2 (P i).toReal =
      (-∑ i, p i * Real.log (p i)) / Real.log 2 := by
    simp only [Real.logb, p, ← mul_div_assoc, ← Finset.sum_div, neg_div]
  rw [hH]
  simp only [Real.logb, Real.log_exp]
  field_simp

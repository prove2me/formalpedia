-- Prove2me | solution 1 for PLCMarkets.ExactCover.lemma_8_2_equilibrium_of_exactCover
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T00:30:32.497248+00:00
-- url     : https://prove2.me/submissions/9f7473e5-6391-47c8-9225-1f7de2349787

import Mathlib
import Definitions.Def_PLCMarkets_ExactCover_X3C
import Definitions.Def_PLCMarkets_ExactCover_MarketD

set_option autoImplicit false

namespace C578ead5

open PLCMarkets.ExactCover

lemma eval_oneSeg (c a t : ℚ) (hc : 0 < c) (ha : 0 ≤ a) (ht : 0 ≤ t) (htc : t ≤ c) (x : ℝ) :
    (PLUtility.oneSeg c a t hc ha ht htc).eval x =
      (c : ℝ) * min (max x 0) (a : ℝ) + (t : ℝ) * max (x - (a : ℝ)) 0 := by
  simp [PLUtility.eval, PLUtility.oneSeg, segEval, PLUtility.length]

lemma eval_flat (x : ℝ) : PLUtility.flat.eval x = 0 := by
  simp [PLUtility.eval, PLUtility.flat, segEval, PLUtility.length]

/-- Supergradient certificate for an optimal bundle (fractional knapsack). -/
lemma opt_of_sg {A G : Type} [Fintype A] [Fintype G] (M : ADMarket A G) (q : G → ℝ) (P : ℝ)
    (hP : 0 < P) (i : A) (y : G → ℝ) (μ : ℝ) (hμ : 0 ≤ μ) (hy0 : ∀ j, 0 ≤ y j)
    (hspend : ∑ j, q j * y j = ∑ j, q j * (M.endow i j : ℝ))
    (hsg : ∀ j t, 0 ≤ t → (M.util i j).eval t ≤ (M.util i j).eval (y j) + μ * q j * (t - y j))
    (hlen : ∀ j, (M.util i j).tail = 0 → y j ≤ ((M.util i j).length : ℝ)) :
    M.IsOptimalBundle (fun j => q j / P) i y := by
  have key : ∀ z : G → ℝ, ∑ j, q j / P * z j = (∑ j, q j * z j) / P := by
    intro z; rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro j _; ring
  refine ⟨hy0, ?_, ?_, hlen⟩
  · unfold ADMarket.income; rw [key, key, hspend]
  · intro z hz hzc
    unfold ADMarket.income at hzc
    rw [key, key, div_le_div_iff_of_pos_right hP] at hzc
    unfold ADMarket.utility
    have h1 : ∑ j, (M.util i j).eval (z j) ≤
        ∑ j, ((M.util i j).eval (y j) + μ * q j * (z j - y j)) :=
      Finset.sum_le_sum fun j _ => hsg j (z j) (hz j)
    have h2 : ∑ j, ((M.util i j).eval (y j) + μ * q j * (z j - y j)) =
        ∑ j, (M.util i j).eval (y j) + μ * (∑ j, q j * z j - ∑ j, q j * y j) := by
      rw [Finset.sum_add_distrib, mul_sub, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      congr 1; apply Finset.sum_congr rfl; intro j _; ring
    have h3 : μ * (∑ j, q j * z j - ∑ j, q j * y j) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hμ (by rw [hspend]; linarith)
    linarith

def goodEquiv (n : ℕ) : Good n ≃ Unit ⊕ (Fin n ⊕ Fin n) where
  toFun g := match g with
    | .zero => Sum.inl ()
    | .set i => Sum.inr (Sum.inl i)
    | .elem j => Sum.inr (Sum.inr j)
  invFun s := match s with
    | Sum.inl _ => .zero
    | Sum.inr (Sum.inl i) => .set i
    | Sum.inr (Sum.inr j) => .elem j
  left_inv g := by cases g <;> rfl
  right_inv s := by rcases s with _ | i | j <;> rfl

lemma sum_good {n : ℕ} (f : Good n → ℝ) :
    ∑ g, f g = f .zero + ∑ i, f (.set i) + ∑ j, f (.elem j) := by
  rw [← (goodEquiv n).symm.sum_comp f]
  simp [Fintype.sum_sum_type, goodEquiv, add_assoc]

def agentEquiv (n : ℕ) : Agent n ≃ Unit ⊕ (Fin n ⊕ (Fin n ⊕ Unit)) where
  toFun g := match g with
    | .regulator => Sum.inl ()
    | .setAgent i => Sum.inr (Sum.inl i)
    | .elemAgent j => Sum.inr (Sum.inr (Sum.inl j))
    | .extra => Sum.inr (Sum.inr (Sum.inr ()))
  invFun s := match s with
    | Sum.inl _ => .regulator
    | Sum.inr (Sum.inl i) => .setAgent i
    | Sum.inr (Sum.inr (Sum.inl j)) => .elemAgent j
    | Sum.inr (Sum.inr (Sum.inr _)) => .extra
  left_inv g := by cases g <;> rfl
  right_inv s := by rcases s with _ | i | j | _ <;> rfl

lemma sum_agent {n : ℕ} (f : Agent n → ℝ) :
    ∑ g, f g = f .regulator + ∑ i, f (.setAgent i) + ∑ j, f (.elemAgent j) + f .extra := by
  rw [← (agentEquiv n).symm.sum_comp f]
  simp [Fintype.sum_sum_type, agentEquiv, add_assoc]

lemma sum_ite_S {n : ℕ} (S : Finset (Fin n)) (a b : ℝ) :
    ∑ i, (if i ∈ S then a else b) = (S.card : ℝ) * a + ((n : ℝ) - S.card) * b := by
  have h : ∀ i : Fin n, (if i ∈ S then a else b) = b + (a - b) * (if i ∈ S then 1 else 0) := by
    intro i; split_ifs <;> ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole]
  simp [Finset.filter_mem_eq_inter]
  ring

/-- Prices before normalization. -/
noncomputable def qD {n : ℕ} (S : Finset (Fin n)) : Good n → ℝ
  | .zero => 1
  | .set i => if i ∈ S then 1 else 1 / 2
  | .elem _ => 1 / 2

/-- The equilibrium allocation. -/
noncomputable def xD {n : ℕ} (C : Fin n → Finset (Fin n)) (S : Finset (Fin n)) :
    Agent n → Good n → ℝ
  | .regulator, .zero => (n : ℝ) ^ 3 - (n : ℝ) / 12
  | .regulator, .set i => if i ∈ S then (n : ℝ) ^ 3 else (n : ℝ) ^ 3 + 1 / 4
  | .regulator, .elem _ => (n : ℝ) ^ 3
  | .setAgent _, .zero => 1 / 2
  | .setAgent i, .set i' => if i' = i ∧ i ∈ S then 1 / 4 else 0
  | .setAgent i, .elem j => if i ∈ S ∧ j ∈ C i then 1 / 6 else 0
  | .elemAgent _, .zero => 1 / 12
  | .elemAgent _, _ => 0
  | .extra, .set _ => 3 / 4
  | .extra, _ => 0

lemma reg_eval (n : ℕ) (x : ℝ) : (regulatorUtil n).eval x =
    2 * min (max x 0) ((n : ℝ) ^ 3) + max (x - (n : ℝ) ^ 3) 0 := by
  simp [regulatorUtil, eval_oneSeg]

lemma util_reg {n : ℕ} (C : Fin n → Finset (Fin n)) (l : Good n) :
    (marketD C).util Agent.regulator l = regulatorUtil n := rfl

section evals
variable {n : ℕ} (C : Fin n → Finset (Fin n)) (t : ℝ)

lemma ev_s0 (i : Fin n) : ((marketD C).util (.setAgent i) .zero).eval t = min (max t 0) (1 / 2) := by
  simp [marketD, utilD, eval_oneSeg]
lemma ev_se (i j : Fin n) : ((marketD C).util (.setAgent i) (.elem j)).eval t =
    if j ∈ C i then 1 / 3 * min (max t 0) (1 / 6) else 0 := by
  simp only [marketD, utilD]; split_ifs <;> simp [eval_oneSeg, eval_flat]
lemma ev_ss (i k : Fin n) : ((marketD C).util (.setAgent i) (.set k)).eval t =
    if k = i then 1 / 9 * min (max t 0) (1 / 4) else 0 := by
  simp only [marketD, utilD]; split_ifs <;> simp [eval_oneSeg, eval_flat]
lemma ev_e0 (j : Fin n) : ((marketD C).util (.elemAgent j) .zero).eval t = min (max t 0) (1 / 12) := by
  simp [marketD, utilD, eval_oneSeg]
lemma ev_es (j k : Fin n) : ((marketD C).util (.elemAgent j) (.set k)).eval t = 0 := by
  simp [marketD, utilD, eval_flat]
lemma ev_ee (j k : Fin n) : ((marketD C).util (.elemAgent j) (.elem k)).eval t = 0 := by
  simp [marketD, utilD, eval_flat]
lemma ev_x0 : ((marketD C).util .extra .zero).eval t = 0 := by
  simp [marketD, utilD, eval_flat]
lemma ev_xe (k : Fin n) : ((marketD C).util .extra (.elem k)).eval t = 0 := by
  simp [marketD, utilD, eval_flat]
lemma ev_xs (k : Fin n) : ((marketD C).util .extra (.set k)).eval t = min (max t 0) (3 / 4) := by
  simp [marketD, utilD, eval_oneSeg]

end evals

lemma reg_opt {n : ℕ} (C : Fin n → Finset (Fin n)) (S : Finset (Fin n))
    (hc : (S.card : ℝ) = (n : ℝ) / 3) (hN : (n : ℝ) / 12 ≤ (n : ℝ) ^ 3)
    (hPpos : (0 : ℝ) < 1 + 7 * (n : ℝ) / 6) :
    (marketD C).IsOptimalBundle (fun g => qD S g / (1 + 7 * (n : ℝ) / 6)) .regulator
      (xD C S .regulator) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hN0 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
  apply opt_of_sg (marketD C) (qD S) _ hPpos _ _ 2 (by norm_num)
  · intro g; cases g <;> simp only [xD] <;> (try split_ifs) <;> linarith
  · rw [sum_good, sum_good]
    have r1 : ∑ i : Fin n, qD S (.set i) * xD C S .regulator (.set i) =
        ∑ i : Fin n, (if i ∈ S then (n : ℝ) ^ 3 else (n : ℝ) ^ 3 / 2 + 1 / 8) :=
      Finset.sum_congr rfl (fun i _ => by simp only [qD, xD]; split_ifs <;> ring)
    have r2 : ∑ i : Fin n, qD S (.set i) * (((marketD C).endow .regulator (.set i) : ℚ) : ℝ) =
        ∑ i : Fin n, (if i ∈ S then (n : ℝ) ^ 3 else (n : ℝ) ^ 3 / 2) :=
      Finset.sum_congr rfl (fun i _ => by
        simp only [qD, marketD, endowD]; push_cast; split_ifs <;> ring)
    rw [r1, r2, sum_ite_S, sum_ite_S]
    simp only [qD, xD, marketD, endowD, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [hc]; ring
  · intro g t ht
    rw [util_reg, reg_eval, reg_eval]
    cases g <;> simp only [xD, qD] <;> (try split_ifs) <;>
      simp only [max_def, min_def] <;> split_ifs <;> linarith
  · intro g htail
    rw [util_reg] at htail
    simp [regulatorUtil, PLUtility.oneSeg] at htail

lemma sum_endow_set {n : ℕ} (C : Fin n → Finset (Fin n)) (S : Finset (Fin n)) (i : Fin n) :
    ∑ k : Fin n, qD S (.set k) * (((marketD C).endow (.setAgent i) (.set k) : ℚ) : ℝ) =
      qD S (.set i) := by
  rw [Finset.sum_eq_single i]
  · simp [marketD, endowD]
  · intro b _ hb; simp [marketD, endowD, hb]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma len_ok {n : ℕ} (C : Fin n → Finset (Fin n)) (S : Finset (Fin n)) (a : Agent n)
    (ha : a ≠ .regulator) (g : Good n) :
    xD C S a g ≤ (((marketD C).util a g).length : ℝ) := by
  cases a with
  | regulator => exact absurd rfl ha
  | setAgent i =>
    cases g <;> simp only [marketD, utilD, xD] <;> (try split_ifs) <;>
      first
      | (exfalso; tauto)
      | (simp [PLUtility.oneSeg, PLUtility.flat, PLUtility.length]; try norm_num)
  | elemAgent j =>
    cases g <;> simp [marketD, utilD, xD, PLUtility.oneSeg, PLUtility.flat,
      PLUtility.length] <;> norm_num
  | extra =>
    cases g <;> simp [marketD, utilD, xD, PLUtility.oneSeg, PLUtility.flat,
      PLUtility.length] <;> norm_num

lemma setIn_opt {n : ℕ} (C : Fin n → Finset (Fin n)) (S : Finset (Fin n))
    (hcard : ∀ i, (C i).card = 3) (i : Fin n) (hi : i ∈ S)
    (hPpos : (0 : ℝ) < 1 + 7 * (n : ℝ) / 6) :
    (marketD C).IsOptimalBundle (fun g => qD S g / (1 + 7 * (n : ℝ) / 6)) (.setAgent i)
      (xD C S (.setAgent i)) := by
  apply opt_of_sg (marketD C) (qD S) _ hPpos _ _ (1 / 9) (by norm_num)
  · intro g; cases g <;> simp only [xD] <;> (try split_ifs) <;> norm_num
  · rw [sum_good, sum_good, sum_endow_set]
    simp [qD, xD, marketD, endowD, hi, hcard, mul_ite, Finset.sum_ite_mem]
    norm_num
  · intro g t ht
    cases g <;> simp only [ev_s0, ev_se, ev_ss, xD, qD, hi, true_and, and_true] <;>
      (try split_ifs) <;> (try simp only [max_def, min_def]) <;> (try split_ifs) <;> linarith
  · intro g _; exact len_ok C S _ (by simp) g

lemma setOut_opt {n : ℕ} (C : Fin n → Finset (Fin n)) (S : Finset (Fin n))
    (i : Fin n) (hi : i ∉ S)
    (hPpos : (0 : ℝ) < 1 + 7 * (n : ℝ) / 6) :
    (marketD C).IsOptimalBundle (fun g => qD S g / (1 + 7 * (n : ℝ) / 6)) (.setAgent i)
      (xD C S (.setAgent i)) := by
  apply opt_of_sg (marketD C) (qD S) _ hPpos _ _ 1 (by norm_num)
  · intro g; cases g <;> simp only [xD] <;> (try split_ifs) <;> norm_num
  · rw [sum_good, sum_good, sum_endow_set]
    simp [qD, xD, marketD, endowD, hi, mul_ite]
  · intro g t ht
    cases g <;> simp only [ev_s0, ev_se, ev_ss, xD, qD, hi, false_and, and_false,
      if_false] <;>
      (try split_ifs) <;> (try simp only [max_def, min_def]) <;> (try split_ifs) <;> linarith
  · intro g _; exact len_ok C S _ (by simp) g

lemma elem_opt {n : ℕ} (C : Fin n → Finset (Fin n)) (S : Finset (Fin n)) (j : Fin n)
    (hPpos : (0 : ℝ) < 1 + 7 * (n : ℝ) / 6) :
    (marketD C).IsOptimalBundle (fun g => qD S g / (1 + 7 * (n : ℝ) / 6)) (.elemAgent j)
      (xD C S (.elemAgent j)) := by
  apply opt_of_sg (marketD C) (qD S) _ hPpos _ _ 1 (by norm_num)
  · intro g; cases g <;> simp only [xD] <;> norm_num
  · rw [sum_good, sum_good]
    simp [qD, xD, marketD, endowD, apply_ite (Rat.cast : ℚ → ℝ)]
    norm_num
  · intro g t ht
    cases g <;> simp only [ev_e0, ev_es, ev_ee, xD, qD] <;>
      (try simp only [max_def, min_def]) <;> (try split_ifs) <;> linarith
  · intro g _; exact len_ok C S _ (by simp) g

lemma extra_opt {n : ℕ} (C : Fin n → Finset (Fin n)) (S : Finset (Fin n))
    (hc : (S.card : ℝ) = (n : ℝ) / 3)
    (hPpos : (0 : ℝ) < 1 + 7 * (n : ℝ) / 6) :
    (marketD C).IsOptimalBundle (fun g => qD S g / (1 + 7 * (n : ℝ) / 6)) .extra
      (xD C S .extra) := by
  apply opt_of_sg (marketD C) (qD S) _ hPpos _ _ 1 (by norm_num)
  · intro g; cases g <;> simp only [xD] <;> norm_num
  · rw [sum_good, sum_good]
    have r1 : ∑ i : Fin n, qD S (.set i) * xD C S .extra (.set i) =
        ∑ i : Fin n, (if i ∈ S then (3 / 4 : ℝ) else 3 / 8) :=
      Finset.sum_congr rfl (fun i _ => by simp only [qD, xD]; split_ifs <;> ring)
    rw [r1, sum_ite_S]
    simp [qD, xD, marketD, endowD]
    rw [hc]; ring
  · intro g t ht
    cases g <;> simp only [ev_x0, ev_xe, ev_xs, xD, qD] <;> (try split_ifs) <;>
      (try simp only [max_def, min_def]) <;> (try split_ifs) <;> linarith
  · intro g _; exact len_ok C S _ (by simp) g

lemma clear {n : ℕ} (C : Fin n → Finset (Fin n)) (S : Finset (Fin n))
    (hone : ∀ j : Fin n, (Finset.univ.filter fun i => i ∈ S ∧ j ∈ C i).card = 1)
    (g : Good n) : ∑ i, xD C S i g = (marketD C).supply g := by
  unfold ADMarket.supply
  rw [sum_agent, sum_agent]
  cases g with
  | zero =>
    simp [xD, marketD, endowD]
    ring
  | set i =>
    have e1 : ∑ k : Fin n, xD C S (.setAgent k) (.set i) = if i ∈ S then 1 / 4 else 0 := by
      rw [Finset.sum_eq_single i]
      · simp [xD]
      · intro b _ hb; simp [xD, Ne.symm hb]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [e1]
    simp [xD, marketD, endowD, apply_ite (Rat.cast : ℚ → ℝ)]
    split_ifs <;> ring
  | elem j =>
    have e1 : ∑ k : Fin n, xD C S (.setAgent k) (.elem j) = 1 / 6 := by
      simp only [xD]
      rw [← Finset.sum_filter, Finset.sum_const, hone j]
      norm_num
    rw [e1]
    simp [xD, marketD, endowD, apply_ite (Rat.cast : ℚ → ℝ)]

end C578ead5

open PLCMarkets.ExactCover in
theorem solution (n : ℕ) (C : Fin n → Finset (Fin n))
    (hcard : ∀ i, (C i).card = 3) (hdiv : 3 ∣ n) (hn : 35 < n)
    (hcover : ∀ x : Fin n, ∃ i, x ∈ C i)
    (hC : HasExactCover C) :
    ∃ p : Good n → ℝ, (marketD C).IsEquilibrium p := by
  classical
  obtain ⟨S, hS⟩ := hC
  -- each element lies in exactly one chosen set
  have hone : ∀ j : Fin n, (Finset.univ.filter fun i => i ∈ S ∧ j ∈ C i).card = 1 := by
    intro j
    obtain ⟨i, hi, huniq⟩ := hS j
    rw [Finset.card_eq_one]
    refine ⟨i, ?_⟩
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hk => huniq k hk, fun hk => hk ▸ hi⟩
  -- 3 |S| = n
  have hS3 : 3 * (S.card : ℝ) = n := by
    have e1 : ∑ j : Fin n, ((Finset.univ.filter fun i => i ∈ S ∧ j ∈ C i).card : ℝ) = n := by
      simp [hone]
    have e2 : ∑ j : Fin n, ((Finset.univ.filter fun i => i ∈ S ∧ j ∈ C i).card : ℝ) =
        ∑ i ∈ S, ((C i).card : ℝ) := by
      simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      rw [Finset.sum_comm]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ S)]
      have : ∀ i ∈ Finset.univ.filter (fun i => i ∉ S),
          (∑ j : Fin n, if i ∈ S ∧ j ∈ C i then (1 : ℝ) else 0) = 0 := by
        intro i hi
        simp only [Finset.mem_filter] at hi
        simp [hi.2]
      rw [Finset.sum_eq_zero this, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
      apply Finset.sum_congr rfl
      intro i hi
      simp [hi]
    rw [e2] at e1
    simp only [hcard, Nat.cast_ofNat, Finset.sum_const, nsmul_eq_mul] at e1
    linarith
  have hc : (S.card : ℝ) = (n : ℝ) / 3 := by linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hN : (n : ℝ) / 12 ≤ (n : ℝ) ^ 3 := by
    have h1 : (n : ℝ) ≤ (n : ℝ) ^ 3 := le_self_pow₀ hn1 (by norm_num)
    linarith
  have hPpos : (0 : ℝ) < 1 + 7 * (n : ℝ) / 6 := by positivity
  refine ⟨fun g => C578ead5.qD S g / (1 + 7 * (n : ℝ) / 6), ⟨⟨?_, ?_⟩, C578ead5.xD C S, ?_,
    C578ead5.clear C S hone⟩⟩
  · intro g
    apply div_nonneg _ hPpos.le
    cases g <;> simp only [C578ead5.qD] <;> (try split_ifs) <;> norm_num
  · rw [← Finset.sum_div, div_eq_one_iff_eq hPpos.ne', C578ead5.sum_good]
    simp only [C578ead5.qD]
    rw [C578ead5.sum_ite_S]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hc]; ring
  · intro i
    cases i with
    | regulator => exact C578ead5.reg_opt C S hc hN hPpos
    | setAgent i =>
      by_cases hi : i ∈ S
      · exact C578ead5.setIn_opt C S hcard i hi hPpos
      · exact C578ead5.setOut_opt C S i hi hPpos
    | elemAgent j => exact C578ead5.elem_opt C S j hPpos
    | extra => exact C578ead5.extra_opt C S hc hPpos

-- Prove2me | solution 1 for ReLUBinaryDepth.ProductTradeoff.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:40:04.44103+00:00
-- url     : https://prove2.me/submissions/3fedff6b-aac7-46ae-90a0-5d5ce109183e

import Mathlib
import Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Construction
import Theorems.Thm_ReLUBinaryDepth_ProductTradeoff_lemma_2_1

section
set_option autoImplicit false

namespace ReLUBinaryDepth.ProductTradeoff.Dev.P22

open ReLUBinaryDepth.ProductTradeoff

theorem sum_pair (len p : ℕ) (hp : p + 1 < len) (c : ℝ) (v : List ℝ) (hv : v.length = len) :
    (∑ j : Fin v.length, (if (j.val = p ∨ j.val = p + 1) then c else 0) * v[j]) =
      c * (v.getD p 0 + v.getD (p + 1) 0) := by
  have h1 : ∀ j : Fin v.length, (if (j.val = p ∨ j.val = p + 1) then c else 0) * v[j] =
      (if j.val = p then c * v.getD p 0 else 0) + (if j.val = p + 1 then c * v.getD (p+1) 0 else 0) := by
    intro j
    have key : v[j] = v.getD j.val 0 := by simp [List.getD_eq_getElem?_getD]
    rw [key]
    by_cases h : j.val = p
    · have : j.val ≠ p + 1 := by omega
      rw [h]; simp [this, h]
    · by_cases h' : j.val = p + 1
      · rw [h']; simp [h, h']
      · simp [h, h']
  rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_add_distrib]
  have e1 : (∑ j : Fin v.length, if j.val = p then c * v.getD p 0 else 0) = c * v.getD p 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun j => if j = p then c * v.getD p 0 else 0)]
    simp; omega
  have e2 : (∑ j : Fin v.length, if j.val = p + 1 then c * v.getD (p+1) 0 else 0) = c * v.getD (p+1) 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun j => if j = p + 1 then c * v.getD (p+1) 0 else 0)]
    simp; omega
  rw [e1, e2]; ring

theorem getD_sum {m : ℕ} (x : Cube m) (c : ℝ) (i : Fin m) :
    (∑ j : Fin m, (if j = i then c else 0) * bit (x j)) = c * bit (x i) := by
  simp [ite_mul, Finset.sum_ite_eq']

theorem gate_eval {n : ℕ} (B : ℝ) (θ : Fin n → Bool → ℝ) (i : Fin n) (b : Bool) (x : Cube n)
    (v : List ℝ) (hlen : v.length = 2 * i.val) (a : ℝ)
    (hprev : 0 < i.val → v.getD (2 * (i.val - 1)) 0 + v.getD (2 * (i.val - 1) + 1) 0 = a)
    (hi0 : i.val = 0 → a = 1) :
    (productStageGate B θ i b).eval x v =
      a * θ i b - (if b then B ^ n * (1 - bit (x i)) else B ^ n * bit (x i)) := by
  unfold AffineGate.eval
  simp only [productStageGate]
  have hin : (∑ j : Fin n, (if j = i then (if b then B ^ n else -(B ^ n)) else 0) * bit (x j)) =
      (if b then B ^ n else -(B ^ n)) * bit (x i) := getD_sum x _ i
  rw [hin]
  by_cases h0 : i.val = 0
  · have ha := hi0 h0
    have hz : (∑ j : Fin v.length, (if 0 < i.val ∧ (j.val = 2 * (i.val - 1) ∨ j.val = 2 * (i.val - 1) + 1)
        then θ i b else 0) * v[j]) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp [h0]
    rw [hz, if_pos h0, ha]
    cases b <;> simp <;> ring
  · have hpos : 0 < i.val := Nat.pos_of_ne_zero h0
    have hs := sum_pair (2 * i.val) (2 * (i.val - 1)) (by omega) (θ i b) v hlen
    have hz : (∑ j : Fin v.length, (if 0 < i.val ∧ (j.val = 2 * (i.val - 1) ∨ j.val = 2 * (i.val - 1) + 1)
        then θ i b else 0) * v[j]) = θ i b * a := by
      have : ∀ j : Fin v.length, (if 0 < i.val ∧ (j.val = 2 * (i.val - 1) ∨ j.val = 2 * (i.val - 1) + 1)
        then θ i b else 0) * v[j] = (if (j.val = 2 * (i.val - 1) ∨ j.val = 2 * (i.val - 1) + 1)
        then θ i b else 0) * v[j] := by
        intro j; simp [hpos]
      rw [Finset.sum_congr rfl (fun j _ => this j), hs, hprev hpos]
    rw [hz, if_neg h0]
    cases b <;> simp <;> ring

def Ls {n : ℕ} (B : ℝ) (θ : Fin n → Bool → ℝ) : List (List (AffineGate n)) :=
  List.ofFn (fun i : Fin n => [productStageGate B θ i false, productStageGate B θ i true])

def vals {n : ℕ} (B : ℝ) (θ : Fin n → Bool → ℝ) (x : Cube n) (k : ℕ) : List ℝ :=
  ((Ls B θ).take k).foldl (fun v layer => v ++ layer.map (fun g => relu (g.eval x v))) []

theorem vals_succ {n : ℕ} (B : ℝ) (θ : Fin n → Bool → ℝ) (x : Cube n) (k : ℕ) (hk : k < n) :
    vals B θ x (k + 1) = vals B θ x k ++
      [relu ((productStageGate B θ ⟨k, hk⟩ false).eval x (vals B θ x k)),
       relu ((productStageGate B θ ⟨k, hk⟩ true).eval x (vals B θ x k))] := by
  unfold vals
  rw [List.take_succ, List.foldl_append]
  have : (Ls B θ)[k]? = some [productStageGate B θ ⟨k, hk⟩ false, productStageGate B θ ⟨k, hk⟩ true] := by
    simp [Ls, List.getElem?_ofFn, hk]
  rw [this]
  simp

theorem acc_succ {n : ℕ} (B : ℝ) (θ : Fin n → Bool → ℝ) (x : Cube n) (k : ℕ) (hk : k < n) :
    accumulator B θ x (k + 1) = selector (θ ⟨k, hk⟩) (B ^ n) (x ⟨k, hk⟩) (accumulator B θ x k) := by
  simp [accumulator, hk]

theorem inv {n : ℕ} (B : ℝ) (θ : Fin n → Bool → ℝ) (x : Cube n) :
    ∀ k, k ≤ n → (vals B θ x k).length = 2 * k ∧
      ∀ i, i < k → (vals B θ x k).getD (2 * i) 0 + (vals B θ x k).getD (2 * i + 1) 0 =
        accumulator B θ x (i + 1) := by
  intro k
  induction k with
  | zero => intro _; simp [vals]
  | succ k ih =>
    intro hk
    have hkn : k < n := by omega
    obtain ⟨hl, hv⟩ := ih (by omega)
    have hcase : ∀ b, relu ((productStageGate B θ ⟨k, hkn⟩ b).eval x (vals B θ x k)) =
        relu (accumulator B θ x k * θ ⟨k, hkn⟩ b - (if b then B ^ n * (1 - bit (x ⟨k, hkn⟩))
          else B ^ n * bit (x ⟨k, hkn⟩))) := by
      intro b
      rw [gate_eval B θ ⟨k, hkn⟩ b x (vals B θ x k) hl (accumulator B θ x k)]
      · intro hpos
        have hpos : 0 < k := hpos
        have := hv (k - 1) (by omega)
        have e : k - 1 + 1 = k := by omega
        rw [e] at this
        exact this
      · intro h0
        have h0 : k = 0 := h0
        subst h0
        simp [accumulator]
    rw [vals_succ B θ x k hkn]
    refine ⟨by simp [hl]; ring, ?_⟩
    intro i hi
    by_cases hik : i < k
    · have h1 : 2 * i < (vals B θ x k).length := by omega
      have h2 : 2 * i + 1 < (vals B θ x k).length := by omega
      rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h2]
      exact hv i hik
    · have hi' : i = k := by omega
      subst hi'
      rw [acc_succ B θ x i hkn]
      have e1 : (vals B θ x i ++ [relu ((productStageGate B θ ⟨i, hkn⟩ false).eval x (vals B θ x i)),
          relu ((productStageGate B θ ⟨i, hkn⟩ true).eval x (vals B θ x i))]).getD (2 * i) 0 =
          relu ((productStageGate B θ ⟨i, hkn⟩ false).eval x (vals B θ x i)) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
        simp [hl]
      have e2 : (vals B θ x i ++ [relu ((productStageGate B θ ⟨i, hkn⟩ false).eval x (vals B θ x i)),
          relu ((productStageGate B θ ⟨i, hkn⟩ true).eval x (vals B θ x i))]).getD (2 * i + 1) 0 =
          relu ((productStageGate B θ ⟨i, hkn⟩ true).eval x (vals B θ x i)) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
        simp [hl]
      rw [e1, e2, hcase, hcase]
      simp [selector]

noncomputable def Fm {n : ℕ} (θ : Fin n → Bool → ℝ) (x : Cube n) (i : ℕ) : ℝ :=
  if h : i < n then θ ⟨i, h⟩ (x ⟨i, h⟩) else 1

theorem acc_facts {n : ℕ} (B : ℝ) (θ : Fin n → Bool → ℝ) (hθ : Admissible B θ) (x : Cube n) :
    ∀ k, k ≤ n → 0 ≤ accumulator B θ x k ∧ accumulator B θ x k ≤ B ^ k ∧
      accumulator B θ x k = ∏ i ∈ Finset.range k, Fm θ x i := by
  obtain ⟨hB, hb⟩ := hθ
  intro k
  induction k with
  | zero => intro _; simp [accumulator]
  | succ k ih =>
    intro hk
    have hkn : k < n := by omega
    obtain ⟨h0, h1, h2⟩ := ih (by omega)
    have hBk : B * accumulator B θ x k ≤ B ^ n := by
      calc B * accumulator B θ x k ≤ B * B ^ k := by
            exact mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = B ^ (k + 1) := by ring
        _ ≤ B ^ n := pow_le_pow_right₀ (le_of_lt hB) (by omega)
    have hsel := ReLUBinaryDepth.ProductTradeoff.lemma_2_1 B (B ^ n) (θ ⟨k, hkn⟩) hB
      (fun b => hb ⟨k, hkn⟩ b) (accumulator B θ x k) h0 hBk
    have hacc : accumulator B θ x (k + 1) = accumulator B θ x k * θ ⟨k, hkn⟩ (x ⟨k, hkn⟩) := by
      rw [acc_succ B θ x k hkn]
      cases hx : x ⟨k, hkn⟩
      · simpa using hsel.1
      · simpa using hsel.2
    have hbd := hb ⟨k, hkn⟩ (x ⟨k, hkn⟩)
    refine ⟨?_, ?_, ?_⟩
    · rw [hacc]; exact mul_nonneg h0 hbd.1
    · rw [hacc, pow_succ]
      exact mul_le_mul h1 hbd.2 hbd.1 (pow_nonneg (by linarith) _)
    · rw [hacc, h2, Finset.prod_range_succ]
      simp [Fm, hkn]

theorem eval_eq {n : ℕ} (B : ℝ) (θ : Fin n → Bool → ℝ) (hθ : Admissible B θ) (x : Cube n) :
    (productNetwork B θ).eval x = accumulator B θ x n := by
  have hlen : (Ls B θ).length = n := by simp [Ls]
  have hvals : (productNetwork B θ).values x = vals B θ x n := by
    unfold vals
    rw [List.take_of_length_le (by omega)]
    rfl
  obtain ⟨hl, hv⟩ := inv B θ x n le_rfl
  obtain ⟨h0, h1, h2⟩ := acc_facts B θ hθ x n le_rfl
  unfold Network.eval
  rw [hvals]
  have ho : (productNetwork B θ).outputRelu = true := rfl
  rw [ho]
  simp only [if_true]
  have hout : (productNetwork B θ).output.eval x (vals B θ x n) = accumulator B θ x n := by
    unfold AffineGate.eval
    simp only [productNetwork]
    by_cases hn : n = 0
    · subst hn
      have : vals B θ x 0 = [] := by simp [vals]
      simp [this, accumulator]
    · have hpos : 0 < n := Nat.pos_of_ne_zero hn
      have hs := sum_pair (2 * n) (2 * (n - 1)) (by omega) 1 (vals B θ x n) hl
      have e : (∑ j : Fin (vals B θ x n).length,
          (if 0 < n ∧ (j.val = 2 * (n - 1) ∨ j.val = 2 * (n - 1) + 1) then (1:ℝ) else 0) *
            (vals B θ x n)[j]) = accumulator B θ x n := by
        have : ∀ j : Fin (vals B θ x n).length,
            (if 0 < n ∧ (j.val = 2 * (n - 1) ∨ j.val = 2 * (n - 1) + 1) then (1:ℝ) else 0) *
              (vals B θ x n)[j] =
            (if (j.val = 2 * (n - 1) ∨ j.val = 2 * (n - 1) + 1) then (1:ℝ) else 0) *
              (vals B θ x n)[j] := by
          intro j; simp [hpos]
        rw [Finset.sum_congr rfl (fun j _ => this j), hs]
        have := hv (n - 1) (by omega)
        have e2 : n - 1 + 1 = n := by omega
        rw [e2] at this
        rw [one_mul]; exact this
      simp only [if_neg hn, zero_mul, Finset.sum_const_zero, zero_add]
      exact e
  rw [hout]
  exact max_eq_right h0

end ReLUBinaryDepth.ProductTradeoff.Dev.P22

namespace ReLUBinaryDepth.ProductTradeoff

open ReLUBinaryDepth.ProductTradeoff.Dev.P22 in
theorem chk_lemma_2_2 (n : ℕ) (B : ℝ) (θ : Fin n → Bool → ℝ) (hθ : Admissible B θ) :
    (productNetwork B θ).depth = n + 1 ∧
    (productNetwork B θ).width ≤ 2 ∧
    (productNetwork B θ).outputRelu = true ∧
    (productNetwork B θ).Computes (productMap θ) ∧
    ∀ x : Cube n,
      accumulator B θ x n = productMap θ x ∧
      (productNetwork B θ).eval x = accumulator B θ x n := by
  have hprod : ∀ x : Cube n, accumulator B θ x n = productMap θ x := by
    intro x
    obtain ⟨_, _, h2⟩ := acc_facts B θ hθ x n le_rfl
    rw [h2]
    unfold productMap
    rw [← Fin.prod_univ_eq_prod_range (Fm θ x) n]
    simp [Fm]
  refine ⟨?_, ?_, rfl, ?_, fun x => ⟨hprod x, eval_eq B θ hθ x⟩⟩
  · simp [Network.depth, productNetwork]
  · have hall : ∀ (L : List (List (AffineGate n))) (w : ℕ), w ≤ 2 → (∀ l ∈ L, l.length ≤ 2) →
        L.foldl (fun w layer => max w layer.length) w ≤ 2 := by
      intro L
      induction L with
      | nil => intro w hw _; simpa using hw
      | cons l L ih =>
        intro w hw hL
        simp only [List.foldl_cons]
        apply ih
        · exact max_le hw (hL l (by simp))
        · intro l' hl'; exact hL l' (by simp [hl'])
    apply hall _ _ (by norm_num)
    intro l hl
    simp [productNetwork, List.mem_ofFn] at hl
    obtain ⟨i, rfl⟩ := hl
    simp
  · intro x
    rw [eval_eq B θ hθ x, hprod x]

end ReLUBinaryDepth.ProductTradeoff
end

theorem solution : type_of% @ReLUBinaryDepth.ProductTradeoff.chk_lemma_2_2 := @ReLUBinaryDepth.ProductTradeoff.chk_lemma_2_2

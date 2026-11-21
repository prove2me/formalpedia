-- Prove2me | solution 1 for ReLUBinaryDepth.ProductTradeoff.Supplement.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:40:04.182202+00:00
-- url     : https://prove2.me/submissions/408417bd-830b-44cf-bb82-b241a931419d

import Mathlib
import Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Supplement_Layered

section
set_option autoImplicit false

namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.L31

open ReLUBinaryDepth.ProductTradeoff

theorem isBitRat_of_abs_le (W : ℕ) (hW : 2 ≤ W) (p : ℤ) (hp : |p| ≤ (W : ℤ)) :
    IsBitRat (2 * Nat.log 2 W) (p : ℝ) := by
  have hlog : 1 ≤ Nat.log 2 W := by
    have : 2 ^ 1 ≤ W := by simpa using hW
    exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).2 this
  have hlt : W < 2 ^ (2 * Nat.log 2 W) := by
    calc W < 2 ^ (Nat.log 2 W).succ := Nat.lt_pow_succ_log_self (by norm_num) W
      _ ≤ 2 ^ (2 * Nat.log 2 W) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨p, 1, by norm_num, ?_, ?_, by simp⟩
  · have : (W : ℤ) < 2 ^ (2 * Nat.log 2 W) := by exact_mod_cast hlt
    omega
  · have : (1 : ℤ) < 2 ^ (2 * Nat.log 2 W) := by
      have : 1 < 2 ^ (2 * Nat.log 2 W) := Nat.one_lt_two_pow (by omega)
      exact_mod_cast this
    simpa using this

def gate {m : ℕ} (a : Fin m → ℤ) (c : ℤ) : AffineGate m where
  bias := (c : ℝ)
  inputWeight := fun j => (a j : ℝ)
  previousWeight := fun _ => 0

def outGate (m : ℕ) : AffineGate m where
  bias := 0
  inputWeight := fun _ => 0
  previousWeight := fun j => if j = 0 then 1 else if j = 1 then -1 else 0

def net {m : ℕ} (a : Fin m → ℤ) (b : ℤ) : Network m where
  layers := [[gate a (1 - b), gate a (-b)]]
  output := outGate m
  outputRelu := true

theorem gate_eval {m : ℕ} (a : Fin m → ℤ) (c : ℤ) (x : Cube m) (v : List ℝ) (hv : v = []) :
    (gate a c).eval x v = (∑ j, (a j : ℝ) * bit (x j)) + c := by
  subst hv
  simp [gate, AffineGate.eval]
  ring

theorem net_eval {m : ℕ} (a : Fin m → ℤ) (b : ℤ) (x : Cube m) :
    (net a b).eval x = relu (relu ((∑ j, (a j : ℝ) * bit (x j)) + (1 - b : ℤ)) -
      relu ((∑ j, (a j : ℝ) * bit (x j)) + (-b : ℤ))) := by
  have hv : (net a b).values x = [relu ((gate a (1 - b)).eval x []), relu ((gate a (-b)).eval x [])] := by
    simp [Network.values, net]
  have ho : (net a b).output = outGate m := rfl
  have hr : (net a b).outputRelu = true := rfl
  unfold Network.eval
  rw [ho, hr, hv]
  simp only [if_true]
  rw [gate_eval _ _ _ _ rfl, gate_eval _ _ _ _ rfl]
  simp [outGate, AffineGate.eval, Fin.sum_univ_two]
  rw [← sub_eq_add_neg]

theorem net_isLayered {m : ℕ} (a : Fin m → ℤ) (b : ℤ) : IsLayered (net a b) := by
  constructor
  · intro k hk hk0
    simp [net] at hk
    omega
  · intro _
    refine ⟨fun i => rfl, ?_⟩
    intro j hj
    simp [net, layerOffset, outGate] at hj ⊢
    by_contra h
    apply hj
    have h0 : j ≠ 0 := by omega
    have h1 : j ≠ 1 := by omega
    simp [h0, h1]

theorem net_bits {m : ℕ} (a : Fin m → ℤ) (b : ℤ) (W : ℕ)
    (h : 2 + |b| + ∑ j, |a j| ≤ (W : ℤ)) :
    HasBitWeights (2 * Nat.log 2 W) (net a b) := by
  have hsum : 0 ≤ ∑ j, |a j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hW2 : 2 ≤ W := by have := abs_nonneg b; omega
  have hb := isBitRat_of_abs_le W hW2
  have hzero : IsBitRat (2 * Nat.log 2 W) 0 := by
    have := hb 0 (by simp)
    simpa using this
  have haj : ∀ j, IsBitRat (2 * Nat.log 2 W) (a j : ℝ) := by
    intro j
    apply hb
    have : |a j| ≤ ∑ j, |a j| :=
      Finset.single_le_sum (f := fun j => |a j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
    have := abs_nonneg b
    omega
  have hc : ∀ c : ℤ, |c| ≤ 1 + |b| → IsBitRat (2 * Nat.log 2 W) (c : ℝ) := by
    intro c hc
    apply hb
    omega
  have gate_ok : ∀ (c : ℤ), |c| ≤ 1 + |b| → ∀ mm, AffineGate.HasBitWeights (2 * Nat.log 2 W) mm (gate a c) := by
    intro c hcb mm
    refine ⟨hc c hcb, haj, fun j _ => ?_⟩
    simpa [gate] using hzero
  constructor
  · intro k hk g hg
    simp only [net] at hk hg
    have hk0 : k = 0 := by simp at hk; omega
    subst hk0
    simp at hg
    rcases hg with rfl | rfl
    · exact gate_ok _ (by
        have : |1 - b| ≤ 1 + |b| := by
          calc |1 - b| ≤ |(1:ℤ)| + |b| := abs_sub _ _
            _ = 1 + |b| := by simp
        exact this) _
    · exact gate_ok _ (by simp) _
  · refine ⟨hzero, fun i => hzero, fun j _ => ?_⟩
    simp only [net, outGate]
    by_cases h0 : j = 0
    · simpa [h0] using hb 1 (by simp; omega)
    · by_cases h1 : j = 1
      · have := hb (-1) (by simp; omega)
        simpa [h1] using this
      · simpa [h0, h1] using hzero

theorem net_bool {m : ℕ} (a : Fin m → ℤ) (b : ℤ) :
    BoolComputes (net a b) (fun y => decide (b ≤ ∑ j, a j * (if y j then 1 else 0))) := by
  intro x
  rw [net_eval]
  beta_reduce
  have hS : (∑ j, (a j : ℝ) * bit (x j)) = ((∑ j, a j * (if x j then 1 else 0) : ℤ) : ℝ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    simp [bit]
  rw [hS]
  generalize (∑ j, a j * (if x j then 1 else 0) : ℤ) = S
  simp only [decide_eq_true_eq]
  by_cases hbS : b ≤ S
  · have h1 : (0 : ℝ) ≤ (S : ℝ) + ((-b : ℤ) : ℝ) := by
      have : (b : ℝ) ≤ S := by exact_mod_cast hbS
      push_cast; linarith
    have h2 : (0 : ℝ) ≤ (S : ℝ) + ((1 - b : ℤ) : ℝ) := by
      have : (b : ℝ) ≤ S := by exact_mod_cast hbS
      push_cast; linarith
    simp only [relu]
    rw [max_eq_right h1, max_eq_right h2]
    have : (S : ℝ) + ((1 - b : ℤ) : ℝ) - ((S : ℝ) + ((-b : ℤ) : ℝ)) = 1 := by push_cast; ring
    rw [this]
    exact ⟨fun _ => hbS, fun _ => by norm_num⟩
  · have hS' : S + 1 ≤ b := by omega
    have : (S : ℝ) + 1 ≤ b := by exact_mod_cast hS'
    have h1 : (S : ℝ) + ((-b : ℤ) : ℝ) ≤ 0 := by push_cast; linarith
    have h2 : (S : ℝ) + ((1 - b : ℤ) : ℝ) ≤ 0 := by push_cast; linarith
    simp only [relu]
    rw [max_eq_left h1, max_eq_left h2]
    simp [hbS]

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.L31

namespace ReLUBinaryDepth.ProductTradeoff.Supplement

open ReLUBinaryDepth.ProductTradeoff
open ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.L31 in
theorem chk_lemma_3_1 :
    ∃ C : ℕ, ∀ (m : ℕ) (a : Fin m → ℤ) (b : ℤ) (W : ℕ),
      2 + |b| + ∑ j, |a j| ≤ (W : ℤ) →
      ∃ N : Network m, IsLayered N ∧ N.outputRelu = true ∧ N.depth = 2 ∧ N.width = 2 ∧
        HasBitWeights (C * Nat.log 2 W) N ∧
        BoolComputes N (fun y => decide (b ≤ ∑ j, a j * (if y j then 1 else 0))) := by
  refine ⟨2, fun m a b W h => ⟨net a b, net_isLayered a b, rfl, rfl, ?_, net_bits a b W h, net_bool a b⟩⟩
  simp [Network.width, net]

end ReLUBinaryDepth.ProductTradeoff.Supplement
end

theorem solution : type_of% @ReLUBinaryDepth.ProductTradeoff.Supplement.chk_lemma_3_1 := @ReLUBinaryDepth.ProductTradeoff.Supplement.chk_lemma_3_1

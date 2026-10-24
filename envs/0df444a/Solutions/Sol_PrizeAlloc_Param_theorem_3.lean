-- Prove2me | solution 1 for PrizeAlloc.Param.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T22:18:11.221999+00:00
-- url     : https://prove2.me/submissions/c68203cb-5a0e-43cb-bfea-7f827de29940

import Mathlib
import Definitions.Def_PrizeAlloc_Param_Setting
import Definitions.Def_PrizeAlloc_Param_ParametricRule
import Theorems.Thm_PrizeAlloc_Interval_lemma_1
import Theorems.Thm_PrizeAlloc_Param_converse
import Theorems.Thm_PrizeAlloc_Param_induction_step

set_option autoImplicit false
open PrizeAlloc.Interval PrizeAlloc.Param

namespace P3Main

variable {U : Type*} [DecidableEq U]

/-- The conclusion of the induction step, for a candidate new function `g`. -/
def Qg (φ : List U → ℝ → U → ℝ) (n : ℕ) (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) : Prop :=
  ContinuousOn g (Set.Ici 0) ∧ MonotoneOn g (Set.Ici 0) ∧
    (∀ x, 0 ≤ x → 0 ≤ g x ∧ g x ≤ f n x) ∧
    ∀ l E, IsRanking l → l.length = n + 1 → 0 ≤ E →
      ∃ x, 0 ≤ x ∧ (∑ k ∈ Finset.Icc 1 l.length, Function.update f (n + 1) g k x) = E ∧
        ∀ i ∈ l, φ l E i = Function.update f (n + 1) g (pos l i) x

/-- The induction hypothesis: `f 1, …, f n` represent `φ` on competitions with `≤ n` competitors. -/
def Pn (φ : List U → ℝ → U → ℝ) (n : ℕ) (f : ℕ → ℝ → ℝ) : Prop :=
  (∀ x, 0 ≤ x → f 1 x = x) ∧
  (∀ k, 1 ≤ k → k ≤ n →
      ContinuousOn (f k) (Set.Ici 0) ∧ MonotoneOn (f k) (Set.Ici 0) ∧ ∀ x, 0 ≤ x → 0 ≤ f k x) ∧
  (∀ k, 1 ≤ k → k < n → ∀ x, 0 ≤ x → f (k + 1) x ≤ f k x) ∧
  (∀ l E, IsRanking l → l.length ≤ n → 0 ≤ E →
      ∃ x, 0 ≤ x ∧ (∑ k ∈ Finset.Icc 1 l.length, f k x) = E ∧ ∀ i ∈ l, φ l E i = f (pos l i) x)

/-- The representations built step by step: `FF φ m` is valid for at most `m + 1` competitors. -/
noncomputable def FF (φ : List U → ℝ → U → ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0 => fun _ x => x
  | m + 1 => Function.update (FF φ m) (m + 2) (Classical.epsilon (Qg φ (m + 1) (FF φ m)))

lemma FF_succ (φ : List U → ℝ → U → ℝ) (m : ℕ) :
    FF φ (m + 1) = Function.update (FF φ m) (m + 2) (Classical.epsilon (Qg φ (m + 1) (FF φ m))) :=
  rfl

lemma FF_stable (φ : List U → ℝ → U → ℝ) (a : ℕ) :
    ∀ d k, k ≤ a + 1 → FF φ (a + d) k = FF φ a k := by
  intro d
  induction d with
  | zero => intro k _; rfl
  | succ d ih =>
    intro k hk
    rw [← Nat.add_assoc, FF_succ, Function.update_of_ne (by omega), ih k hk]

lemma FF_diag (φ : List U → ℝ → U → ℝ) (m k : ℕ) (hk : k ≤ m + 1) : FF φ m k = FF φ k k := by
  rcases Nat.lt_or_ge m k with h | h
  · have hk' : k = m + 1 := by omega
    subst hk'
    have := FF_stable φ m 1 (m + 1) le_rfl
    exact this.symm
  · have := FF_stable φ k (m - k) k (by omega)
    rw [show k + (m - k) = m by omega] at this
    exact this

end P3Main

open P3Main

theorem solution {U : Type*} [DecidableEq U] [Countable U]
    (hU : ∃ a b c : U, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (φ : List U → ℝ → U → ℝ) (hφ : PrizeAlloc.Interval.IsPrizeRule φ) :
    (PrizeAlloc.Interval.Anonymous φ ∧ PrizeAlloc.Interval.OrderPreserving φ ∧
      PrizeAlloc.Interval.WinnerStrictMonotone φ ∧ TopConsistent φ) ↔
      IsParamRule φ := by
  classical
  constructor
  swap
  · intro hpar
    exact PrizeAlloc.Param.converse φ hφ hpar
  rintro ⟨hA, hOP, hWSM, hTC⟩
  have hEC : EndowmentContinuous φ := PrizeAlloc.Interval.lemma_1 φ hφ hWSM.1
  -- base case: one competitor
  have hbase : Pn φ 1 (FF φ 0) := by
    refine ⟨fun x _ => rfl, ?_, ?_, ?_⟩
    · intro k _ _
      exact ⟨continuousOn_id, monotoneOn_id, fun x hx => hx⟩
    · intro k hk hk'; omega
    · intro l E hl hlen hE
      have hlen1 : l.length = 1 := le_antisymm hlen (List.length_pos_iff.mpr hl.2)
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen1
      refine ⟨E, hE, by simp [FF], ?_⟩
      intro i hi
      have hia : i = a := List.mem_singleton.mp hi
      subst hia
      have := (hφ [i] E hl hE).2
      simpa [FF] using this
  -- induction step
  have hstep : ∀ n, 1 ≤ n → ∀ f, Pn φ n f → ∀ g, Qg φ n f g → Pn φ (n + 1) (Function.update f (n + 1) g) := by
    intro n hn f ⟨hf1, hfk, hfdec, hrule⟩ g ⟨hgc, hgm, hgb, hgr⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx
      rw [Function.update_of_ne (by omega)]
      exact hf1 x hx
    · intro k hk hkn
      rcases Nat.lt_or_ge k (n + 1) with h | h
      · rw [Function.update_of_ne (by omega)]
        exact hfk k hk (by omega)
      · have : k = n + 1 := by omega
        subst this
        rw [Function.update_self]
        exact ⟨hgc, hgm, fun x hx => (hgb x hx).1⟩
    · intro k hk hkn x hx
      rcases Nat.lt_or_ge k n with h | h
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hfdec k hk h x hx
      · have : k = n := by omega
        subst this
        rw [Function.update_self, Function.update_of_ne (by omega)]
        exact (hgb x hx).2
    · intro l E hl hlen hE
      rcases Nat.lt_or_ge l.length (n + 1) with h | h
      · obtain ⟨x, hx, hxs, hxφ⟩ := hrule l E hl (by omega) hE
        refine ⟨x, hx, ?_, ?_⟩
        · rw [← hxs]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Function.update_of_ne (by have := (Finset.mem_Icc.mp hk).2; omega)]
        · intro i hi
          have hpl : pos l i ≤ l.length := by
            have := List.idxOf_lt_length_of_mem hi
            unfold pos; omega
          rw [Function.update_of_ne (by omega)]
          exact hxφ i hi
      · exact hgr l E hl (by omega) hE
  -- all stages
  have hall : ∀ m, Pn φ (m + 1) (FF φ m) := by
    intro m
    induction m with
    | zero => exact hbase
    | succ m ih =>
      have hex : ∃ g, Qg φ (m + 1) (FF φ m) g := by
        obtain ⟨hf1, hfk, hfdec, hrule⟩ := ih
        exact PrizeAlloc.Param.induction_step φ hφ hA hOP hWSM hTC hEC (m + 1) (by omega)
          (FF φ m) hf1 hfk hfdec hrule
      rw [FF_succ]
      exact hstep (m + 1) (by omega) _ ih _ (Classical.epsilon_spec hex)
  -- the limiting representation
  let f : ℕ → ℝ → ℝ := fun k => FF φ k k
  refine ⟨f, ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    show FF φ 1 1 x = x
    rw [← FF_diag φ 0 1 le_rfl]
    rfl
  · intro k hk
    obtain ⟨-, hfk, hfdec, -⟩ := hall k
    refine ⟨(hfk k hk (by omega)).1, (hfk k hk (by omega)).2.1, fun x hx => ⟨(hfk k hk (by omega)).2.2 x hx, ?_⟩⟩
    show FF φ (k + 1) (k + 1) x ≤ FF φ k k x
    rw [← FF_diag φ k (k + 1) le_rfl]
    exact hfdec k hk (by omega) x hx
  · intro l E hl hE
    have hL : 1 ≤ l.length := List.length_pos_iff.mpr hl.2
    obtain ⟨-, -, -, hrule⟩ := hall (l.length - 1)
    obtain ⟨x, hx, hxs, hxφ⟩ := hrule l E hl (by omega) hE
    refine ⟨x, hx, ?_, ?_⟩
    · rw [← hxs]
      apply Finset.sum_congr rfl
      intro k hk
      show FF φ k k x = FF φ (l.length - 1) k x
      rw [FF_diag φ (l.length - 1) k (by have := (Finset.mem_Icc.mp hk).2; omega)]
    · intro i hi
      have hpl : pos l i ≤ l.length := by
        have := List.idxOf_lt_length_of_mem hi
        unfold pos; omega
      rw [hxφ i hi]
      show FF φ (l.length - 1) (pos l i) x = FF φ (pos l i) (pos l i) x
      rw [FF_diag φ (l.length - 1) (pos l i) (by omega)]

-- Prove2me | solution 1 for SuttonBartoRL.BatchTD.batch_mc_converges_to_sample_average
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T01:53:04.534759+00:00
-- url     : https://prove2.me/submissions/41035791-7abb-4325-aea5-25a330bde310

import Mathlib
import Definitions.Def_SuttonBartoRL_BatchTD_Episodes
import Definitions.Def_SuttonBartoRL_BatchTD_BatchUpdating

set_option autoImplicit false

open Filter Topology

namespace P035640ab
open SuttonBartoRL.BatchTD

lemma ep_eq {S : Type} [DecidableEq S] (e : Episode S) (s : S) (r : ℕ → ℝ) (V : S → ℝ) :
    (∑ t ∈ Finset.range e.length,
        if stateAt e t = some s then r t - extV V (stateAt e t) else 0)
      = (∑ t ∈ Finset.range e.length, if stateAt e t = some s then r t else 0)
        - (((Finset.range e.length).filter fun t => stateAt e t = some s).card : ℝ) * V s := by
  have h : ∀ t, (if stateAt e t = some s then r t - extV V (stateAt e t) else 0)
      = (if stateAt e t = some s then r t else 0) - (if stateAt e t = some s then V s else 0) := by
    intro t
    split_ifs with ht
    · simp [ht, extV]
    · simp
  rw [Finset.sum_congr rfl (fun t _ => h t), Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

lemma mcInc_eq {S : Type} [Fintype S] [DecidableEq S] (γ : ℝ) (b : Batch S) (V : S → ℝ)
    (s : S) :
    mcIncrement γ b V s = visitSum b s (fun e t => ret γ e t) - (visitCount b s : ℝ) * V s := by
  unfold mcIncrement visitSum visitCount
  induction b with
  | nil => simp
  | cons e b ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    rw [ih, ep_eq e s (fun t => ret γ e t) V]
    ring

lemma visitSum_zero {S : Type} [Fintype S] [DecidableEq S] (b : Batch S) (s : S)
    (f : Episode S → ℕ → ℝ) (h : visitCount b s = 0) : visitSum b s f = 0 := by
  unfold visitSum
  unfold visitCount at h
  induction b with
  | nil => simp
  | cons e b ih =>
    simp only [List.map_cons, List.sum_cons] at h ⊢
    have h1 := (Nat.add_eq_zero_iff.mp h).1
    have h2 := (Nat.add_eq_zero_iff.mp h).2
    rw [ih h2, ← Finset.sum_filter, Finset.card_eq_zero.mp h1]
    simp

lemma step {S : Type} [Fintype S] [DecidableEq S] (α γ : ℝ) (b : Batch S) (V₀ : S → ℝ)
    (s : S) (m : ℕ) :
    batchMC α γ b V₀ (m + 1) s = batchMC α γ b V₀ m s
      + α * (visitSum b s (fun e t => ret γ e t) - (visitCount b s : ℝ) * batchMC α γ b V₀ m s) := by
  rw [← mcInc_eq]
  simp only [batchMC, Function.iterate_succ_apply']
  rfl

end P035640ab

open Filter Topology SuttonBartoRL.BatchTD in
theorem solution {S : Type} [Fintype S] [DecidableEq S]
    (b : Batch S) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ∃ αbar : ℝ, 0 < αbar ∧ ∀ α : ℝ, 0 < α → α < αbar → ∀ (V₀ : S → ℝ) (s : S),
      Tendsto (fun m : ℕ => batchMC α γ b V₀ m s) atTop
        (𝓝 (if visitCount b s = 0 then V₀ s else mcAverage γ b s)) := by
  set T : ℝ := ∑ s, (visitCount b s : ℝ) with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  refine ⟨1 / (1 + T), by positivity, ?_⟩
  intro α hα hαb V₀ s
  set G := visitSum b s (fun e t => ret γ e t) with hG
  set n : ℝ := (visitCount b s : ℝ) with hn
  split_ifs with h0
  · have hG0 : G = 0 := P035640ab.visitSum_zero b s _ h0
    have hconst : ∀ m, batchMC α γ b V₀ m s = V₀ s := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [P035640ab.step, ih, ← hG, hG0, h0]
        simp
    simp only [hconst]
    exact tendsto_const_nhds
  · have hnpos : 0 < n := by rw [hn]; exact_mod_cast Nat.pos_of_ne_zero h0
    have hnT : n ≤ T := by
      exact Finset.single_le_sum (f := fun s => (visitCount b s : ℝ))
        (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ s)
    have hα1 : α * (1 + T) < 1 := by
      have h1T : (0:ℝ) < 1 + T := by linarith
      exact (lt_div_iff₀ h1T).mp hαb
    have hαn : α * n < 1 := by nlinarith
    have hαn0 : 0 < α * n := mul_pos hα hnpos
    have hn' : n * (G / n) = G := mul_div_cancel₀ _ hnpos.ne'
    have hclosed : ∀ m, batchMC α γ b V₀ m s
        = G / n + (1 - α * n) ^ m * (V₀ s - G / n) := by
      intro m
      induction m with
      | zero => simp [batchMC]
      | succ m ih =>
        rw [P035640ab.step, ← hG, ← hn, ih, pow_succ]
        linear_combination (-α) * hn'
    have hlim : Tendsto (fun m : ℕ => G / n + (1 - α * n) ^ m * (V₀ s - G / n)) atTop
        (𝓝 (G / n + 0 * (V₀ s - G / n))) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)).mul_const _).const_add _
    rw [zero_mul, add_zero] at hlim
    simp only [hclosed]
    exact hlim

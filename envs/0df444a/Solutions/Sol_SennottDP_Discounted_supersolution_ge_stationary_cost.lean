-- Prove2me | solution 1 for SennottDP.Discounted.supersolution_ge_stationary_cost
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T06:34:23.08166+00:00
-- url     : https://prove2.me/submissions/fa1db0de-fbd6-47d1-b5b0-4b91db35d277

import Mathlib
import Definitions.Def_SennottDP_Discounted_Optimality

set_option autoImplicit false

open scoped ENNReal NNReal
open Filter Topology

namespace P2M94cc13fb

open SennottDP.Discounted

variable {S : Type} [Countable S] {Act : Type}

lemma tsum_snoc {β : Type} {n : ℕ} (f : (Fin (n + 1) → β) → ℝ≥0∞) :
    ∑' s, f s = ∑' s : Fin n → β, ∑' x : β, f (Fin.snoc s x) := by
  rw [← (Fin.snocEquiv (fun _ => β)).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
  rfl

open Classical in
lemma dist_eq (M : MDC S Act) (e : StationaryPolicy M) (n : ℕ) (s : Fin (n + 1) → S)
    (as : Fin n → Act) (a : Act) :
    e.toPolicy.dist n s as a = if a = e.1 (s (Fin.last n)) then 1 else 0 := rfl

lemma expState_zero (M : MDC S Act) (θ : Policy M) (i : S) (W : S → ℝ≥0∞) :
    expState M θ i 0 W = W i := by
  unfold expState
  rw [tsum_snoc]
  simp only [histProb]
  have h1 : ∀ x : S, (Fin.snoc (fun k : Fin 0 => Fin.elim0 k) x : Fin 1 → S) 0 = x := fun x => rfl
  rw [tsum_eq_single (fun k : Fin 0 => Fin.elim0 k)]
  · rw [tsum_eq_single i]
    · simp [h1]
    · intro x hx
      simp [h1, hx]
  · intro b hb
    exact absurd (Subsingleton.elim b _) hb

open Classical in
lemma expState_succ (M : MDC S Act) (e : StationaryPolicy M) (i : S) (n : ℕ)
    (W : S → ℝ≥0∞) :
    expState M e.toPolicy i (n + 1) W =
      expState M e.toPolicy i n (fun j => ∑' k, M.P j (e.1 j) k * W k) := by
  calc expState M e.toPolicy i (n + 1) W
      = ∑' s : Fin (n + 1) → S, ∑' j : S, ∑' as : Fin n → Act, ∑' a : Act,
          histProb M e.toPolicy i n s as * (if a = e.1 (s (Fin.last n)) then 1 else 0) *
            M.P (s (Fin.last n)) a j * W j := by
        unfold expState
        rw [tsum_snoc]
        refine tsum_congr fun s => tsum_congr fun j => ?_
        rw [tsum_snoc]
        refine tsum_congr fun as => tsum_congr fun a => ?_
        simp only [histProb, Fin.init_snoc, Fin.snoc_last, Fin.snoc_castSucc, dist_eq]
    _ = ∑' s : Fin (n + 1) → S, ∑' as : Fin n → Act, histProb M e.toPolicy i n s as *
          ∑' k, M.P (s (Fin.last n)) (e.1 (s (Fin.last n))) k * W k := by
        refine tsum_congr fun s => ?_
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun as => ?_
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun j => ?_
        rw [tsum_eq_single (e.1 (s (Fin.last n)))]
        · simp [mul_assoc]
        · intro a ha
          simp [ha]
    _ = _ := rfl

open Classical in
lemma expCost_stat (M : MDC S Act) (e : StationaryPolicy M) (i : S) (t : ℕ) :
    expCost M e.toPolicy i t = expState M e.toPolicy i t (fun j => (M.C j (e.1 j) : ℝ≥0∞)) := by
  unfold expCost expState
  refine tsum_congr fun s => tsum_congr fun as => ?_
  congr 1
  simp [dist_eq, ite_mul, e.2 (s (Fin.last t))]

lemma expState_add_mul (M : MDC S Act) (θ : Policy M) (i : S) (n : ℕ) (f g : S → ℝ≥0∞)
    (c : ℝ≥0∞) :
    expState M θ i n (fun j => f j + c * g j) =
      expState M θ i n f + c * expState M θ i n g := by
  unfold expState
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine tsum_congr fun s => ?_
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine tsum_congr fun as => ?_
  ring

lemma expState_mono (M : MDC S Act) (θ : Policy M) (i : S) (n : ℕ) (f g : S → ℝ≥0∞)
    (h : ∀ j, f j ≤ g j) : expState M θ i n f ≤ expState M θ i n g := by
  unfold expState
  refine ENNReal.tsum_le_tsum fun s => ENNReal.tsum_le_tsum fun as => ?_
  gcongr
  exact h _

theorem key (M : MDC S Act) (α : ℝ≥0) (W : S → ℝ≥0∞) (e : StationaryPolicy M)
    (hW : ∀ i, bellmanQ M α W i (e.1 i) ≤ W i) (i : S) (n : ℕ) :
    finiteHorizonCost M e.toPolicy α n i + (α : ℝ≥0∞) ^ n * expState M e.toPolicy i n W
      ≤ W i := by
  induction n with
  | zero => simp [finiteHorizonCost, expState_zero]
  | succ n ih =>
    have h1 : finiteHorizonCost M e.toPolicy α (n + 1) i =
        finiteHorizonCost M e.toPolicy α n i + (α : ℝ≥0∞) ^ n * expCost M e.toPolicy i n := by
      simp only [finiteHorizonCost, Finset.sum_range_succ]
    have h2 : expCost M e.toPolicy i n + (α : ℝ≥0∞) * expState M e.toPolicy i (n + 1) W
        ≤ expState M e.toPolicy i n W := by
      rw [expCost_stat, expState_succ, ← expState_add_mul]
      exact expState_mono _ _ _ _ _ _ (fun j => hW j)
    calc finiteHorizonCost M e.toPolicy α (n + 1) i
          + (α : ℝ≥0∞) ^ (n + 1) * expState M e.toPolicy i (n + 1) W
        = finiteHorizonCost M e.toPolicy α n i + (α : ℝ≥0∞) ^ n *
            (expCost M e.toPolicy i n + (α : ℝ≥0∞) * expState M e.toPolicy i (n + 1) W) := by
          rw [h1, pow_succ, mul_add, add_assoc, mul_assoc]
      _ ≤ finiteHorizonCost M e.toPolicy α n i
            + (α : ℝ≥0∞) ^ n * expState M e.toPolicy i n W := by gcongr
      _ ≤ W i := ih

end P2M94cc13fb

open SennottDP.Discounted NNReal ENNReal in
theorem solution {S : Type} [Countable S] {Act : Type} (M : MDC S Act)
    (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1) (W : S → ℝ≥0∞) (e : StationaryPolicy M)
    (hW : ∀ i, bellmanQ M α W i (e.1 i) ≤ W i) :
    (∀ i : S, ∀ n : ℕ, 1 ≤ n →
        finiteHorizonCost M e.toPolicy α n i + (α : ℝ≥0∞) ^ n * expState M e.toPolicy i n W
          ≤ W i) ∧
      ∀ i : S, discountedCost M e.toPolicy α i ≤ W i := by
  refine ⟨fun i n _ => P2M94cc13fb.key M α W e hW i n, fun i => ?_⟩
  unfold discountedCost
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun n => ?_
  exact le_trans le_self_add (P2M94cc13fb.key M α W e hW i n)

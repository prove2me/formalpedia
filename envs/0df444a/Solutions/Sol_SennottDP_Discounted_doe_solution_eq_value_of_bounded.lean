-- Prove2me | solution 1 for SennottDP.Discounted.doe_solution_eq_value_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-03T22:08:22.946918+00:00
-- url     : https://prove2.me/submissions/d0150b72-fb1c-49a4-9a07-188d485a0b56

import Mathlib
import Definitions.Def_SennottDP_Discounted_Optimality
import Theorems.Thm_SennottDP_Discounted_supersolution_ge_stationary_cost
import Theorems.Thm_SennottDP_Discounted_finite_horizon_cost_tendsto

set_option autoImplicit false


open scoped ENNReal NNReal
open Filter Topology
-- Uses the accepted public supersolution theorem by Nickrobbins95, submission
-- fa1db0de-fbd6-47d1-b5b0-4b91db35d277. Its expectation helpers are adapted
-- below in namespace Accepted; the original accepted source is preserved in the bundle.

-- Adapted helpers from Nickrobbins95, accepted submission fa1db0de-fbd6-47d1-b5b0-4b91db35d277.

set_option autoImplicit false

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.Discounted.Accepted

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

end SennottDP.Discounted.Accepted


namespace SennottDP.Discounted
open scoped ENNReal NNReal
open Filter Topology
noncomputable section
variable {S : Type} [Countable S] {Act : Type}

def bm_history (M : MDC S Act) (θ : Policy M) (i : S) (n : ℕ)
    (F : (Fin (n+1) → S) → (Fin n → Act) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' s, ∑' as, histProb M θ i n s as*F s as

lemma bm_history_mono (M : MDC S Act) (θ : Policy M) (i : S) (n : ℕ)
    (F G : (Fin (n+1) → S) → (Fin n → Act) → ℝ≥0∞)
    (h : ∀ s as, F s as ≤ G s as) : bm_history M θ i n F ≤ bm_history M θ i n G := by
  exact ENNReal.tsum_le_tsum (fun s => ENNReal.tsum_le_tsum (fun as => by gcongr; exact h s as))

lemma bm_history_add_mul (M : MDC S Act) (θ : Policy M) (i : S) (n : ℕ)
    (F G : (Fin (n+1) → S) → (Fin n → Act) → ℝ≥0∞) (c : ℝ≥0∞) :
    bm_history M θ i n (fun s as => F s as+c*G s as)=
      bm_history M θ i n F+c*bm_history M θ i n G := by
  unfold bm_history
  rw [← ENNReal.tsum_mul_left,← ENNReal.tsum_add]
  refine tsum_congr (fun s => ?_)
  rw [← ENNReal.tsum_mul_left,← ENNReal.tsum_add]
  refine tsum_congr (fun as => ?_)
  ring

lemma bm_expState_succ (M : MDC S Act) (θ : Policy M) (i : S) (n : ℕ) (W : S → ℝ≥0∞) :
    expState M θ i (n+1) W = bm_history M θ i n (fun s as =>
      ∑ a ∈ M.A (s (Fin.last n)), θ.dist n s as a *
        ∑' j, M.P (s (Fin.last n)) a j*W j) := by
  classical
  calc
    _ = ∑' s : Fin (n+1) → S, ∑' j : S, ∑' as : Fin n → Act, ∑' a : Act,
        histProb M θ i n s as*θ.dist n s as a*M.P (s (Fin.last n)) a j*W j := by
      unfold expState
      rw [Accepted.tsum_snoc]
      refine tsum_congr (fun s => tsum_congr (fun j => ?_))
      rw [Accepted.tsum_snoc]
      refine tsum_congr (fun as => tsum_congr (fun a => ?_))
      simp only [histProb,Fin.init_snoc,Fin.snoc_last,Fin.snoc_castSucc]
    _ = ∑' s : Fin (n+1) → S, ∑' as : Fin n → Act, histProb M θ i n s as*
        ∑' a : Act, θ.dist n s as a*∑' j, M.P (s (Fin.last n)) a j*W j := by
      refine tsum_congr (fun s => ?_)
      rw [ENNReal.tsum_comm]
      refine tsum_congr (fun as => ?_)
      rw [ENNReal.tsum_comm]
      calc
        _ = ∑' a : Act, (histProb M θ i n s as*θ.dist n s as a)*
            ∑' j, M.P (s (Fin.last n)) a j*W j := by
          refine tsum_congr (fun a => ?_)
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr (fun j => ?_)
          ring
        _ = _ := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr (fun a => ?_)
          ring
    _ = _ := by
      refine tsum_congr (fun s => tsum_congr (fun as => ?_))
      congr 1
      apply tsum_eq_sum
      intro a ha
      simp [θ.dist_supp n s as a ha]

lemma bm_expState_one (M : MDC S Act) (θ : Policy M) (i : S) (n : ℕ) :
    expState M θ i n (fun _ => 1)=1 := by
  induction n with
  | zero => exact Accepted.expState_zero M θ i _
  | succ n ih =>
    rw [bm_expState_succ]
    have hh : ∀ s as, (∑ a ∈ M.A (s (Fin.last n)), θ.dist n s as a*
        ∑' j, M.P (s (Fin.last n)) a j*(1:ℝ≥0∞))=1 := by
      intro s as
      simp only [mul_one]
      calc
        _ = ∑ a ∈ M.A (s (Fin.last n)), θ.dist n s as a*1 := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [M.P_sum _ _ ha]
        _ = 1 := by simpa using θ.dist_sum n s as
    simp_rw [hh]
    exact ih

lemma bm_expState_const (M : MDC S Act) (θ : Policy M) (i : S) (n : ℕ) (c : ℝ≥0∞) :
    expState M θ i n (fun _ => c)=c := by
  have h := Accepted.expState_add_mul M θ i n (fun _ => 0) (fun _ => 1) c
  have hz : expState M θ i n (fun _ => 0)=0 := by simp [expState]
  simpa [hz,bm_expState_one] using h

lemma bm_expState_bound (M : MDC S Act) (θ : Policy M) (i : S) (n : ℕ)
    (W : S → ℝ≥0∞) (c : ℝ≥0∞) (hW : ∀ j, W j ≤ c) : expState M θ i n W ≤ c := by
  exact (Accepted.expState_mono M θ i n W (fun _ => c) hW).trans_eq
    (bm_expState_const M θ i n c)

lemma bm_stage_inequality (M : MDC S Act) (θ : Policy M) (α : ℝ≥0) (i : S) (n : ℕ)
    (U W : S → ℝ≥0∞) (hUW : ∀ s as,
      U (s (Fin.last n)) ≤ ∑ a ∈ M.A (s (Fin.last n)), θ.dist n s as a *
        bellmanQ M α W (s (Fin.last n)) a) :
    expState M θ i n U ≤ expCost M θ i n+(α : ℝ≥0∞)*expState M θ i (n+1) W := by
  rw [bm_expState_succ]
  change bm_history M θ i n (fun s _ => U (s (Fin.last n))) ≤
    bm_history M θ i n (fun s as => ∑ a ∈ M.A (s (Fin.last n)),
      θ.dist n s as a*(M.C (s (Fin.last n)) a : ℝ≥0∞)) +
    (α : ℝ≥0∞)*bm_history M θ i n (fun s as => ∑ a ∈ M.A (s (Fin.last n)),
      θ.dist n s as a*∑' j, M.P (s (Fin.last n)) a j*W j)
  rw [← bm_history_add_mul]
  apply bm_history_mono
  intro s as
  calc
    _ ≤ _ := hUW s as
    _ = _ := by
      simp only [bellmanQ,mul_add,Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

end
end SennottDP.Discounted


namespace SennottDP.Discounted
open scoped ENNReal NNReal
open Filter Topology
noncomputable section
variable {S : Type} [Countable S] {Act : Type}

lemma bm_Q_mono (M : MDC S Act) (α : ℝ≥0) (U W : S → ℝ≥0∞)
    (h : ∀ j, U j ≤ W j) (i : S) (a : Act) : bellmanQ M α U i a ≤ bellmanQ M α W i a := by
  have hs : (∑' j, M.P i a j*U j) ≤ ∑' j, M.P i a j*W j :=
    ENNReal.tsum_le_tsum (fun j => by gcongr; exact h j)
  unfold bellmanQ
  gcongr

lemma bm_bellman_mono (M : MDC S Act) (α : ℝ≥0) (U W : S → ℝ≥0∞)
    (h : ∀ j, U j ≤ W j) (i : S) : bellman M α U i ≤ bellman M α W i := by
  apply Finset.le_inf'
  intro a ha
  exact (Finset.inf'_le _ ha).trans (bm_Q_mono M α U W h i a)

lemma bm_selector (M : MDC S Act) (α : ℝ≥0) (W : S → ℝ≥0∞) :
    ∃ f : StationaryPolicy M, Realizes M f α W := by
  classical
  have hh : ∀ i, ∃ a ∈ M.A i, bellmanQ M α W i a=bellman M α W i := by
    intro i
    obtain ⟨a,ha,hval⟩ := Finset.exists_mem_eq_inf' (M.A_nonempty i) (bellmanQ M α W i)
    exact ⟨a,ha,hval.symm⟩
  choose f hf hmin using hh
  exact ⟨⟨f,hf⟩,hmin⟩

lemma bm_tsum_iSup {ι : Type*} (f : ℕ → ι → ℝ≥0∞) (hf : ∀ i, Monotone (fun n => f n i)) :
    (∑' i, ⨆ n, f n i)=⨆ n, ∑' i, f n i := by
  classical
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  have hh (s : Finset ι) : (∑ i ∈ s, ⨆ n, f n i)=⨆ n, ∑ i ∈ s, f n i :=
    ENNReal.finsetSum_iSup_of_monotone hf
  simp_rw [hh]
  rw [iSup_comm]

lemma bm_Q_iSup (M : MDC S Act) (α : ℝ≥0) (U : ℕ → S → ℝ≥0∞)
    (hU : ∀ j, Monotone (fun n => U n j)) (i : S) (a : Act) :
    bellmanQ M α (fun j => ⨆ n, U n j) i a=⨆ n, bellmanQ M α (U n) i a := by
  unfold bellmanQ
  simp_rw [ENNReal.mul_iSup]
  rw [bm_tsum_iSup (fun n j => M.P i a j*U n j)
    (fun j r s hrs => mul_le_mul_right (hU j hrs) (M.P i a j))]
  rw [ENNReal.mul_iSup,ENNReal.add_iSup]

lemma bm_inf'_mono {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f g : ι → ℝ≥0∞) (h : ∀ a ∈ s, f a ≤ g a) : s.inf' hs f ≤ s.inf' hs g := by
  apply Finset.le_inf'
  intro a ha
  exact (Finset.inf'_le _ ha).trans (h a ha)

lemma bm_inf'_iSup {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ℕ → ι → ℝ≥0∞)
    (hf : ∀ a ∈ s, Monotone (fun n => f n a)) :
    s.inf' hs (fun a => ⨆ n, f n a)=⨆ n, s.inf' hs (f n) := by
  classical
  induction s using Finset.cons_induction with
  | empty => exact (Finset.not_nonempty_empty hs).elim
  | cons a s ha ih =>
    by_cases he : s.Nonempty
    · have hf' : ∀ a ∈ s, Monotone (fun n => f n a) := fun a h => hf a (Finset.mem_cons_of_mem h)
      have hm : Monotone (fun n => s.inf' he (f n)) :=
        fun r t hrt => bm_inf'_mono s he _ _ (fun a ha => hf' a ha hrt)
      rw [Finset.inf'_cons he,ih he hf']
      rw [← iSup_inf_of_monotone (hf a (Finset.mem_cons_self _ _)) hm]
      apply iSup_congr
      intro n
      rw [Finset.inf'_cons he]
    · have hse : s=∅ := Finset.not_nonempty_iff_eq_empty.mp he
      subst s
      simp

lemma bm_bellman_iSup (M : MDC S Act) (α : ℝ≥0) (U : ℕ → S → ℝ≥0∞)
    (hU : ∀ j, Monotone (fun n => U n j)) (i : S) :
    bellman M α (fun j => ⨆ n, U n j) i=⨆ n, bellman M α (U n) i := by
  unfold bellman
  simp_rw [bm_Q_iSup M α U hU]
  exact bm_inf'_iSup _ _ _ (fun a _ r s hrs => bm_Q_mono M α _ _ (fun j => hU j hrs) i a)

def bm_iter (M : MDC S Act) (α : ℝ≥0) : ℕ → S → ℝ≥0∞
  | 0 => fun _ => 0
  | n+1 => bellman M α (bm_iter M α n)

lemma bm_iter_mono (M : MDC S Act) (α : ℝ≥0) (i : S) : Monotone (fun n => bm_iter M α n i) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n generalizing i with
  | zero => exact bot_le
  | succ n ih => exact bm_bellman_mono M α _ _ ih i

def bm_limit (M : MDC S Act) (α : ℝ≥0) (i : S) : ℝ≥0∞ := ⨆ n, bm_iter M α n i

lemma bm_limit_fixed (M : MDC S Act) (α : ℝ≥0) (i : S) :
    bm_limit M α i=bellman M α (bm_limit M α) i := by
  unfold bm_limit
  rw [bm_bellman_iSup M α (bm_iter M α) (bm_iter_mono M α)]
  change (⨆ n, bm_iter M α n i)=⨆ n, bm_iter M α (n+1) i
  apply le_antisymm
  · apply iSup_le
    intro n
    exact (bm_iter_mono M α i (Nat.le_succ n)).trans
      (le_iSup (fun n => bm_iter M α (n+1) i) n)
  · apply iSup_le
    intro n
    exact le_iSup (fun n => bm_iter M α n i) (n+1)

end
end SennottDP.Discounted


namespace SennottDP.Discounted
open scoped ENNReal NNReal
open Filter Topology
noncomputable section
variable {S : Type} [Countable S] {Act : Type}

lemma bm_average_min (M : MDC S Act) (θ : Policy M) (α : ℝ≥0) (W : S → ℝ≥0∞)
    (n : ℕ) (s : Fin (n+1) → S) (as : Fin n → Act) :
    bellman M α W (s (Fin.last n)) ≤ ∑ a ∈ M.A (s (Fin.last n)), θ.dist n s as a*
      bellmanQ M α W (s (Fin.last n)) a := by
  have he : (∑ a ∈ M.A (s (Fin.last n)), θ.dist n s as a*bellman M α W (s (Fin.last n)))=
      bellman M α W (s (Fin.last n)) := by
    rw [← Finset.sum_mul,θ.dist_sum,one_mul]
  rw [← he]
  apply Finset.sum_le_sum
  intro a ha
  have hh := Finset.inf'_le (bellmanQ M α W (s (Fin.last n))) ha
  exact mul_le_mul_right hh (θ.dist n s as a)

lemma bm_iter_cost_tail (M : MDC S Act) (θ : Policy M) (α : ℝ≥0) (N : ℕ) (i : S)
    (k : ℕ) (hk : k ≤ N) :
    bm_iter M α N i ≤ finiteHorizonCost M θ α k i + (α : ℝ≥0∞)^k*
      expState M θ i k (bm_iter M α (N-k)) := by
  induction k with
  | zero => simp [finiteHorizonCost,Accepted.expState_zero]
  | succ k ih =>
    have hNk : N-k=(N-(k+1))+1 := by omega
    have hh := bm_stage_inequality M θ α i k (bm_iter M α (N-k))
      (bm_iter M α (N-(k+1))) (by
        rw [hNk]
        exact bm_average_min M θ α _ k)
    calc
      _ ≤ finiteHorizonCost M θ α k i+(α : ℝ≥0∞)^k*
          expState M θ i k (bm_iter M α (N-k)) := ih (by omega)
      _ ≤ finiteHorizonCost M θ α k i+(α : ℝ≥0∞)^k*
          (expCost M θ i k+(α : ℝ≥0∞)*expState M θ i (k+1) (bm_iter M α (N-(k+1)))) := by
        gcongr
      _ = _ := by
        simp only [finiteHorizonCost,Finset.sum_range_succ,pow_succ,mul_add,mul_assoc,add_assoc]

lemma bm_iter_le_finite_cost (M : MDC S Act) (θ : Policy M) (α : ℝ≥0) (N : ℕ) (i : S) :
    bm_iter M α N i ≤ finiteHorizonCost M θ α N i := by
  have h := bm_iter_cost_tail M θ α N i N le_rfl
  simpa [bm_iter,expState] using h

lemma bm_finite_le_cost (M : MDC S Act) (θ : Policy M) (α : ℝ≥0) (N : ℕ) (i : S) :
    finiteHorizonCost M θ α N i ≤ discountedCost M θ α i := by
  exact ENNReal.sum_le_tsum (Finset.range N)

lemma bm_limit_le_value (M : MDC S Act) (α : ℝ≥0) (i : S) : bm_limit M α i ≤ valueFn M α i := by
  apply iSup_le
  intro n
  apply le_iInf
  intro θ
  exact (bm_iter_le_finite_cost M θ α n i).trans (bm_finite_le_cost M θ α n i)

lemma bm_value_eq_limit (M : MDC S Act) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1) :
    valueFn M α=bm_limit M α := by
  obtain ⟨f,hf⟩ := bm_selector M α (bm_limit M α)
  have hbound : ∀ i, bellmanQ M α (bm_limit M α) i (f.1 i) ≤ bm_limit M α i :=
    fun i => (hf i).trans (bm_limit_fixed M α i).symm |>.le
  have hc := (supersolution_ge_stationary_cost M α hα0 hα1 (bm_limit M α) f hbound).2
  ext i
  exact le_antisymm ((iInf_le _ f.toPolicy).trans (hc i)) (bm_limit_le_value M α i)

lemma bm_value_fixed (M : MDC S Act) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1) (i : S) :
    valueFn M α i=bellman M α (valueFn M α) i := by
  rw [bm_value_eq_limit M α hα0 hα1]
  exact bm_limit_fixed M α i

lemma bm_realizes_optimal (M : MDC S Act) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1)
    (f : StationaryPolicy M) (hf : Realizes M f α (valueFn M α)) : IsDiscountOptimal M f.toPolicy α := by
  have hh : ∀ i, bellmanQ M α (valueFn M α) i (f.1 i) ≤ valueFn M α i :=
    fun i => (hf i).trans (bm_value_fixed M α hα0 hα1 i).symm |>.le
  have hc := (supersolution_ge_stationary_cost M α hα0 hα1 (valueFn M α) f hh).2
  intro i
  exact le_antisymm (hc i) (iInf_le _ f.toPolicy)

lemma bm_supersolution_value (M : MDC S Act) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1)
    (W : S → ℝ≥0∞) (hW : ∀ i, bellman M α W i ≤ W i) : ∀ i, valueFn M α i ≤ W i := by
  obtain ⟨f,hf⟩ := bm_selector M α W
  have hQ : ∀ i, bellmanQ M α W i (f.1 i) ≤ W i := fun i => (hf i).le.trans (hW i)
  have hc := (supersolution_ge_stationary_cost M α hα0 hα1 W f hQ).2
  intro i
  exact (iInf_le (fun θ => discountedCost M θ α i) f.toPolicy).trans (hc i)

lemma bm_root (M : MDC S Act) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ i : S, valueFn M α i=bellman M α (valueFn M α) i) ∧
    (∀ W : S → ℝ≥0∞, (∀ i, W i=bellman M α W i) → ∀ i, valueFn M α i ≤ W i) ∧
    (∀ f : StationaryPolicy M, Realizes M f α (valueFn M α) → IsDiscountOptimal M f.toPolicy α) := by
  refine ⟨bm_value_fixed M α hα0 hα1,?_,bm_realizes_optimal M α hα0 hα1⟩
  intro W hW
  exact bm_supersolution_value M α hα0 hα1 W (fun i => (hW i).symm.le)

end
end SennottDP.Discounted


namespace SennottDP.Discounted
open scoped ENNReal NNReal
open Filter Topology
noncomputable section
variable {S : Type} [Countable S] {Act : Type}

lemma bm_stat_equality (M : MDC S Act) (α : ℝ≥0) (W : S → ℝ≥0∞) (f : StationaryPolicy M)
    (hW : ∀ i, bellmanQ M α W i (f.1 i)=W i) (i : S) (n : ℕ) :
    finiteHorizonCost M f.toPolicy α n i + (α : ℝ≥0∞)^n*expState M f.toPolicy i n W=W i := by
  induction n with
  | zero => simp [finiteHorizonCost,Accepted.expState_zero]
  | succ n ih =>
    have h1 : finiteHorizonCost M f.toPolicy α (n+1) i=
        finiteHorizonCost M f.toPolicy α n i+(α : ℝ≥0∞)^n*expCost M f.toPolicy i n := by
      simp only [finiteHorizonCost,Finset.sum_range_succ]
    have h2 : expCost M f.toPolicy i n+(α : ℝ≥0∞)*expState M f.toPolicy i (n+1) W=
        expState M f.toPolicy i n W := by
      rw [Accepted.expCost_stat,Accepted.expState_succ,← Accepted.expState_add_mul]
      congr 1
      funext j
      exact hW j
    calc
      _ = finiteHorizonCost M f.toPolicy α n i+(α : ℝ≥0∞)^n*
          (expCost M f.toPolicy i n+(α : ℝ≥0∞)*expState M f.toPolicy i (n+1) W) := by
        rw [h1,pow_succ,mul_add,add_assoc,mul_assoc]
      _ = W i := by rw [h2,ih]

lemma bm_tail_zero (M : MDC S Act) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1)
    (f : StationaryPolicy M) (hf : Realizes M f α (valueFn M α)) (i : S)
    (hi : valueFn M α i < ⊤) :
    Tendsto (fun n : ℕ => (α : ℝ≥0∞)^n*expState M f.toPolicy i n (valueFn M α)) atTop (𝓝 0) := by
  have hopt := bm_realizes_optimal M α hα0 hα1 f hf
  have hQ : ∀ j, bellmanQ M α (valueFn M α) j (f.1 j)=valueFn M α j :=
    fun j => (hf j).trans (bm_value_fixed M α hα0 hα1 j).symm
  have he (n : ℕ) : (α : ℝ≥0∞)^n*expState M f.toPolicy i n (valueFn M α)=
      valueFn M α i-finiteHorizonCost M f.toPolicy α n i :=
    ENNReal.eq_sub_of_add_eq' hi.ne (by rw [add_comm]; exact bm_stat_equality M α _ f hQ i n)
  simp_rw [he]
  have hlim := (finite_horizon_cost_tendsto M α hα0 hα1 f.toPolicy i).2
  rw [hopt i] at hlim
  have hh := (ENNReal.continuous_sub_left hi.ne).tendsto (valueFn M α i) |>.comp hlim
  simpa only [Function.comp_def,tsub_self] using hh

end
end SennottDP.Discounted


namespace SennottDP.Discounted
open scoped ENNReal NNReal
open Filter Topology
noncomputable section
variable {S : Type} [Countable S] {Act : Type}

lemma bm_stat_upper (M : MDC S Act) (α : ℝ≥0) (W : S → ℝ≥0∞) (f : StationaryPolicy M)
    (hW : ∀ j, W j ≤ bellmanQ M α W j (f.1 j)) (i : S) (n : ℕ) :
    W i ≤ finiteHorizonCost M f.toPolicy α n i+(α : ℝ≥0∞)^n*expState M f.toPolicy i n W := by
  induction n with
  | zero => simp [finiteHorizonCost,Accepted.expState_zero]
  | succ n ih =>
    have h1 : finiteHorizonCost M f.toPolicy α (n+1) i=
        finiteHorizonCost M f.toPolicy α n i+(α : ℝ≥0∞)^n*expCost M f.toPolicy i n := by
      simp only [finiteHorizonCost,Finset.sum_range_succ]
    have h2 : expState M f.toPolicy i n W ≤
        expCost M f.toPolicy i n+(α : ℝ≥0∞)*expState M f.toPolicy i (n+1) W := by
      rw [Accepted.expCost_stat,Accepted.expState_succ,← Accepted.expState_add_mul]
      exact Accepted.expState_mono _ _ _ _ _ _ hW
    calc
      _ ≤ finiteHorizonCost M f.toPolicy α n i+(α : ℝ≥0∞)^n*expState M f.toPolicy i n W := ih
      _ ≤ finiteHorizonCost M f.toPolicy α n i+(α : ℝ≥0∞)^n*
          (expCost M f.toPolicy i n+(α : ℝ≥0∞)*expState M f.toPolicy i (n+1) W) := by gcongr
      _ = _ := by rw [h1,pow_succ,mul_add,add_assoc,mul_assoc]

lemma bm_liminf_const_add (a : ℝ≥0∞) (u : ℕ → ℝ≥0∞) :
    liminf (fun n => a+u n) atTop=a+liminf u atTop := by
  simp only [liminf_eq_iSup_iInf_of_nat']
  rw [ENNReal.add_iSup]
  apply iSup_congr
  intro n
  rw [ENNReal.add_iInf]

lemma bm_liminf_unique (M : MDC S Act) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1)
    (W : S → ℝ≥0∞) (hW : ∀ i, W i=bellman M α W i) (f : StationaryPolicy M)
    (hf : Realizes M f α (valueFn M α))
    (hlim : ∀ i, liminf (fun n : ℕ => (α : ℝ≥0∞)^n*expState M f.toPolicy i n W) atTop=0) :
    W=valueFn M α := by
  have hopt := bm_realizes_optimal M α hα0 hα1 f hf
  have hQ : ∀ j, W j ≤ bellmanQ M α W j (f.1 j) :=
    fun j => (hW j).le.trans (Finset.inf'_le _ (f.2 j))
  have hmin := bm_supersolution_value M α hα0 hα1 W (fun j => (hW j).symm.le)
  ext i
  apply le_antisymm
  · have hn : ∀ n, W i ≤ valueFn M α i+(α : ℝ≥0∞)^n*expState M f.toPolicy i n W := by
      intro n
      calc
        _ ≤ _ := bm_stat_upper M α W f hQ i n
        _ ≤ _ := by
          rw [← hopt i]
          gcongr
          exact bm_finite_le_cost M f.toPolicy α n i
    have hh := le_liminf_of_le (f := atTop) (u := fun n => valueFn M α i+(α : ℝ≥0∞)^n*expState M f.toPolicy i n W)
      (by isBoundedDefault) (Eventually.of_forall hn)
    simpa only [bm_liminf_const_add,hlim,add_zero] using hh
  · exact hmin i

end
end SennottDP.Discounted


namespace SennottDP.Discounted
open scoped ENNReal NNReal
open Filter Topology
noncomputable section
variable {S : Type} [Countable S] {Act : Type}

lemma bm_bounded_unique (M : MDC S Act) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1)
    (W : S → ℝ≥0∞) (hfinite : ∀ i, W i ≠ ⊤) (hW : ∀ i, W i=bellman M α W i)
    (B : ℝ≥0) (hB : ∀ i, W i ≤ valueFn M α i+B) : W=valueFn M α := by
  obtain ⟨f,hf⟩ := bm_selector M α (valueFn M α)
  have hmin := bm_supersolution_value M α hα0 hα1 W (fun i => (hW i).symm.le)
  have hpow : Tendsto (fun n : ℕ => (α : ℝ≥0∞)^n*(B : ℝ≥0∞)) atTop (𝓝 0) := by
    have hp := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (α : ℝ≥0∞)) (by exact_mod_cast hα1)
    have hh := ENNReal.Tendsto.mul_const hp (Or.inr (ENNReal.coe_ne_top : (B : ℝ≥0∞) ≠ ⊤))
    simpa only [zero_mul] using hh
  apply bm_liminf_unique M α hα0 hα1 W hW f hf
  intro i
  have hi : valueFn M α i < ⊤ := lt_of_le_of_lt (hmin i) (lt_top_iff_ne_top.mpr (hfinite i))
  have htail := bm_tail_zero M α hα0 hα1 f hf i hi
  have hupper : ∀ n, (α : ℝ≥0∞)^n*expState M f.toPolicy i n W ≤
      (α : ℝ≥0∞)^n*expState M f.toPolicy i n (valueFn M α)+(α : ℝ≥0∞)^n*B := by
    intro n
    have hh := Accepted.expState_mono M f.toPolicy i n W (fun j => valueFn M α j+B) hB
    have he : expState M f.toPolicy i n (fun j => valueFn M α j+B)=
        expState M f.toPolicy i n (valueFn M α)+B := by
      have he' := Accepted.expState_add_mul M f.toPolicy i n (valueFn M α) (fun _ => 1) B
      simpa [bm_expState_one] using he'
    rw [he] at hh
    simpa only [mul_add] using mul_le_mul_right hh ((α : ℝ≥0∞)^n)
  have hsum : Tendsto (fun n => (α : ℝ≥0∞)^n*expState M f.toPolicy i n (valueFn M α)+
      (α : ℝ≥0∞)^n*B) atTop (𝓝 0) := by
    simpa only [add_zero] using htail.add hpow
  have hlim : Tendsto (fun n : ℕ => (α : ℝ≥0∞)^n*expState M f.toPolicy i n W) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => bot_le) hupper
  exact hlim.liminf_eq

lemma bm_bounded_root (M : MDC S Act) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ W : S → ℝ≥0∞, (∀ i, W i ≠ ⊤) → (∀ i, W i=bellman M α W i) →
      (∃ B : ℝ≥0, ∀ i, W i ≤ valueFn M α i+B) → W=valueFn M α) ∧
    (∀ W : S → ℝ≥0∞, (∀ i, W i=bellman M α W i) →
      (∃ B : ℝ≥0, ∀ i, W i ≤ B) → W=valueFn M α) := by
  refine ⟨?_,?_⟩
  · intro W hfinite hW
    rintro ⟨B,hB⟩
    exact bm_bounded_unique M α hα0 hα1 W hfinite hW B hB
  · intro W hW
    rintro ⟨B,hB⟩
    have hfinite : ∀ i, W i ≠ ⊤ := fun i => ne_of_lt ((hB i).trans_lt ENNReal.coe_lt_top)
    have hh : ∀ i, W i ≤ valueFn M α i+B := fun i => (hB i).trans le_add_self
    exact bm_bounded_unique M α hα0 hα1 W hfinite hW B hh

end
end SennottDP.Discounted

open SennottDP.Discounted

/-- Sennott (1999), Corollary 4.2.4, p. 66: (i) if `W` is a finite nonnegative solution of the
discount optimality equation (4.9) with `W ≤ V_α + B` for some finite constant `B`, then
`W = V_α`; (ii) if `W` is a nonnegative bounded solution of (4.9), then `W = V_α`.
A constant `B < 0` gives `W ≤ V_α ≤ V_α + 0`, so `B` ranges over `[0, ∞)` without loss. -/
theorem solution {S : Type} [Countable S] {Act : Type} (M : MDC S Act)
    (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ W : S → ℝ≥0∞, (∀ i, W i ≠ ⊤) → (∀ i, W i = bellman M α W i) →
        (∃ B : ℝ≥0, ∀ i, W i ≤ valueFn M α i + B) → W = valueFn M α) ∧
      (∀ W : S → ℝ≥0∞, (∀ i, W i = bellman M α W i) →
        (∃ B : ℝ≥0, ∀ i, W i ≤ B) → W = valueFn M α) := by
  exact bm_bounded_root M α hα0 hα1

#print axioms solution

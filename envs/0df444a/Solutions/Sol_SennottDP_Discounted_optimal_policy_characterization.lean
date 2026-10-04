-- Prove2me | solution 1 for SennottDP.Discounted.optimal_policy_characterization
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-03T22:18:35.658965+00:00
-- url     : https://prove2.me/submissions/99d2378f-b83d-451f-bf1a-13ad5f664e4f

import Mathlib
import Definitions.Def_SennottDP_Discounted_Optimality
import Theorems.Thm_SennottDP_Discounted_supersolution_ge_stationary_cost

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

open Classical in
def bm_markovPolicy (M : MDC S Act) (g : ℕ → StationaryPolicy M) : Policy M where
  dist n s _ a := if a = (g n).1 (s (Fin.last n)) then 1 else 0
  dist_supp n s _ a ha := by
    have hne : a ≠ (g n).1 (s (Fin.last n)) := fun h => ha (h ▸ (g n).2 _)
    simp [hne]
  dist_sum n s _ := by simp [(g n).2 (s (Fin.last n))]

lemma bm_markov_average (M : MDC S Act) (g : ℕ → StationaryPolicy M) (n : ℕ)
    (s : Fin (n+1) → S) (as : Fin n → Act) (F : Act → ℝ≥0∞) :
    (∑ a ∈ M.A (s (Fin.last n)), (bm_markovPolicy M g).dist n s as a*F a)=
      F ((g n).1 (s (Fin.last n))) := by
  classical
  simp [bm_markovPolicy,(g n).2 (s (Fin.last n))]

lemma bm_stage_equality (M : MDC S Act) (θ : Policy M) (α : ℝ≥0) (i : S) (n : ℕ)
    (U W : S → ℝ≥0∞) (hUW : ∀ s as,
      U (s (Fin.last n)) = ∑ a ∈ M.A (s (Fin.last n)), θ.dist n s as a *
        bellmanQ M α W (s (Fin.last n)) a) :
    expState M θ i n U = expCost M θ i n+(α : ℝ≥0∞)*expState M θ i (n+1) W := by
  rw [bm_expState_succ]
  change bm_history M θ i n (fun s _ => U (s (Fin.last n))) =
    bm_history M θ i n (fun s as => ∑ a ∈ M.A (s (Fin.last n)),
      θ.dist n s as a*(M.C (s (Fin.last n)) a : ℝ≥0∞)) +
    (α : ℝ≥0∞)*bm_history M θ i n (fun s as => ∑ a ∈ M.A (s (Fin.last n)),
      θ.dist n s as a*∑' j, M.P (s (Fin.last n)) a j*W j)
  rw [← bm_history_add_mul]
  unfold bm_history
  apply tsum_congr
  intro s
  apply tsum_congr
  intro as
  congr 1
  dsimp only
  rw [hUW s as]
  simp only [bellmanQ,mul_add,Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma bm_finite_attainment (M : MDC S Act) (α : ℝ≥0) (N : ℕ) :
    ∃ θ : Policy M, ∀ i, finiteHorizonCost M θ α N i=bm_iter M α N i := by
  classical
  choose fs hfs using (fun n : ℕ => bm_selector M α (bm_iter M α n))
  let g : ℕ → StationaryPolicy M := fun t => fs (N-t-1)
  let θ := bm_markovPolicy M g
  have he (i : S) (k : ℕ) (hk : k ≤ N) :
      finiteHorizonCost M θ α k i+(α : ℝ≥0∞)^k*
        expState M θ i k (bm_iter M α (N-k))=bm_iter M α N i := by
    induction k with
    | zero => simp [finiteHorizonCost,Accepted.expState_zero]
    | succ k ih =>
      have hNk : N-k=(N-(k+1))+1 := by omega
      have hh := bm_stage_equality M θ α i k (bm_iter M α (N-k))
        (bm_iter M α (N-(k+1))) (by
          intro s as
          rw [bm_markov_average]
          have hindex : N-k-1=N-(k+1) := by omega
          change bm_iter M α (N-k) (s (Fin.last k))=
            bellmanQ M α (bm_iter M α (N-(k+1))) (s (Fin.last k))
              ((fs (N-k-1)).1 (s (Fin.last k)))
          rw [hindex,hfs,hNk]
          rfl)
      calc
        _ = finiteHorizonCost M θ α k i+(α : ℝ≥0∞)^k*
            (expCost M θ i k+(α : ℝ≥0∞)*expState M θ i (k+1) (bm_iter M α (N-(k+1)))) := by
          simp only [finiteHorizonCost,Finset.sum_range_succ,pow_succ,mul_add,mul_assoc,add_assoc]
        _ = _ := by rw [← hh]; exact ih (by omega)
  refine ⟨θ,fun i => ?_⟩
  simpa [bm_iter,expState] using he i N le_rfl

lemma bm_finite_value (M : MDC S Act) (α : ℝ≥0) (n : ℕ) (i : S) :
    finiteValueFn M α n i=bm_iter M α n i := by
  obtain ⟨θ,hθ⟩ := bm_finite_attainment M α n
  apply le_antisymm
  · exact (iInf_le _ θ).trans_eq (hθ i)
  · exact le_iInf (fun θ => bm_iter_le_finite_cost M θ α n i)

lemma bm_iteration (M : MDC S Act) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ i : S, Monotone (fun n : ℕ => finiteValueFn M α n i) ∧
        Tendsto (fun n : ℕ => finiteValueFn M α n i) atTop (𝓝 (valueFn M α i))) ∧
      ∀ fs : ℕ → StationaryPolicy M,
        (∀ n : ℕ, 1 ≤ n → Realizes M (fs n) α (finiteValueFn M α (n - 1))) →
        ∀ f : StationaryPolicy M, IsLimitPoint M fs f →
          IsDiscountOptimal M f.toPolicy α := by
  refine ⟨?_,?_⟩
  · intro i
    simp_rw [bm_finite_value]
    refine ⟨bm_iter_mono M α i,?_⟩
    rw [bm_value_eq_limit M α hα0 hα1]
    exact tendsto_atTop_iSup (bm_iter_mono M α i)
  · intro fs hfs f hf
    obtain ⟨r,hr,heq⟩ := hf
    apply bm_realizes_optimal M α hα0 hα1 f
    intro i
    apply le_antisymm
    · rw [bm_value_eq_limit M α hα0 hα1]
      rw [← bm_limit_fixed M α i]
      change bellmanQ M α (fun j => ⨆ n, bm_iter M α n j) i (f.1 i) ≤ bm_limit M α i
      rw [bm_Q_iSup M α (bm_iter M α) (bm_iter_mono M α)]
      apply iSup_le
      intro n
      obtain ⟨K,hK⟩ := eventually_atTop.mp (heq i)
      let k := K+n+1
      have hkn : n+1 ≤ r k := (by omega : n+1 ≤ k).trans (hr.id_le k)
      have hkK : K ≤ k := by dsimp [k]; omega
      have hreal := hfs (r k) (by omega)
      have hmin : bellmanQ M α (finiteValueFn M α (r k-1)) i ((fs (r k)).1 i)=
          bellman M α (finiteValueFn M α (r k-1)) i := hreal i
      have hfinitefun : finiteValueFn M α (r k-1)=bm_iter M α (r k-1) :=
        funext (bm_finite_value M α (r k-1))
      rw [hfinitefun] at hmin
      rw [hK k hkK] at hmin
      calc
        _ ≤ bellmanQ M α (bm_iter M α (r k-1)) i (f.1 i) :=
          bm_Q_mono M α _ _ (fun j => bm_iter_mono M α j (by omega)) i (f.1 i)
        _ = bm_iter M α (r k) i := by
          rw [hmin]
          have hn : r k=(r k-1)+1 := by omega
          conv_rhs => rw [hn]
          rfl
        _ ≤ bm_limit M α i := le_iSup (fun n => bm_iter M α n i) (r k)
    · exact Finset.inf'_le _ (f.2 i)

end
end SennottDP.Discounted


namespace SennottDP.Discounted
open scoped ENNReal NNReal
open Filter Topology
noncomputable section
variable {S : Type} [Countable S] {Act : Type}

lemma bm_history_iSup (M : MDC S Act) (θ : Policy M) (i : S) (n : ℕ)
    (F : ℕ → (Fin (n+1) → S) → (Fin n → Act) → ℝ≥0∞)
    (hF : ∀ s as, Monotone (fun N => F N s as)) :
    bm_history M θ i n (fun s as => ⨆ N, F N s as)=⨆ N, bm_history M θ i n (F N) := by
  unfold bm_history
  simp_rw [ENNReal.mul_iSup]
  have he (s : Fin (n+1) → S) :
      (∑' as, ⨆ N, histProb M θ i n s as*F N s as)=
        ⨆ N, ∑' as, histProb M θ i n s as*F N s as :=
    bm_tsum_iSup _ (fun as r t hrt => mul_le_mul_right (hF s as hrt) _)
  simp_rw [he]
  exact bm_tsum_iSup _ (fun s r t hrt => ENNReal.tsum_le_tsum
    (fun as => mul_le_mul_right (hF s as hrt) _))

lemma bm_future_iter_bound (M : MDC S Act) (θ : Policy M) (α : ℝ≥0)
    (i : S) (n N k : ℕ) (hk : k ≤ N) :
    finiteHorizonCost M θ α n i+(α : ℝ≥0∞)^n*expState M θ i n (bm_iter M α N) ≤
      finiteHorizonCost M θ α (n+k) i+(α : ℝ≥0∞)^(n+k)*
        expState M θ i (n+k) (bm_iter M α (N-k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hNk : N-k=(N-(k+1))+1 := by omega
    have hh := bm_stage_inequality M θ α i (n+k) (bm_iter M α (N-k))
      (bm_iter M α (N-(k+1))) (by
        rw [hNk]
        exact bm_average_min M θ α _ (n+k))
    calc
      _ ≤ finiteHorizonCost M θ α (n+k) i+(α : ℝ≥0∞)^(n+k)*
          expState M θ i (n+k) (bm_iter M α (N-k)) := ih (by omega)
      _ ≤ finiteHorizonCost M θ α (n+k) i+(α : ℝ≥0∞)^(n+k)*
          (expCost M θ i (n+k)+(α : ℝ≥0∞)*expState M θ i (n+k+1) (bm_iter M α (N-(k+1)))) := by gcongr
      _ = _ := by
        simp only [finiteHorizonCost,Finset.sum_range_succ,pow_succ,mul_add,mul_assoc,add_assoc,Nat.add_succ]

lemma bm_prefix_value_le_cost (M : MDC S Act) (θ : Policy M) (α : ℝ≥0)
    (hα0 : 0 < α) (hα1 : α < 1) (i : S) (n : ℕ) :
    finiteHorizonCost M θ α n i+(α : ℝ≥0∞)^n*expState M θ i n (valueFn M α) ≤
      discountedCost M θ α i := by
  rw [bm_value_eq_limit M α hα0 hα1]
  change finiteHorizonCost M θ α n i+(α : ℝ≥0∞)^n*
    bm_history M θ i n (fun s _ => ⨆ N, bm_iter M α N (s (Fin.last n))) ≤ _
  rw [bm_history_iSup M θ i n _ (fun s _ => bm_iter_mono M α (s (Fin.last n))),
    ENNReal.mul_iSup,ENNReal.add_iSup]
  apply iSup_le
  intro N
  have hh := bm_future_iter_bound M θ α i n N N le_rfl
  have hz : expState M θ i (n+N) (bm_iter M α 0)=0 := by simp [bm_iter,expState]
  simp only [Nat.sub_self,hz,mul_zero,add_zero] at hh
  exact hh.trans (bm_finite_le_cost M θ α (n+N) i)

lemma bm_value_le_prefix (M : MDC S Act) (θ : Policy M) (α : ℝ≥0)
    (hα0 : 0 < α) (hα1 : α < 1) (i : S) (n : ℕ) :
    valueFn M α i ≤ finiteHorizonCost M θ α n i+(α : ℝ≥0∞)^n*
      expState M θ i n (valueFn M α) := by
  induction n with
  | zero => simp [finiteHorizonCost,Accepted.expState_zero]
  | succ n ih =>
    have hh := bm_stage_inequality M θ α i n (valueFn M α) (valueFn M α) (by
      intro s as
      rw [bm_value_fixed M α hα0 hα1]
      exact bm_average_min M θ α _ n s as)
    calc
      _ ≤ finiteHorizonCost M θ α n i+(α : ℝ≥0∞)^n*expState M θ i n (valueFn M α) := ih
      _ ≤ finiteHorizonCost M θ α n i+(α : ℝ≥0∞)^n*
          (expCost M θ i n+(α : ℝ≥0∞)*expState M θ i (n+1) (valueFn M α)) := by gcongr
      _ = _ := by
        simp only [finiteHorizonCost,Finset.sum_range_succ,pow_succ,mul_add,mul_assoc,add_assoc]

lemma bm_policy_average (M : MDC S Act) (θ : Policy M) (α : ℝ≥0)
    (i : S) (n : ℕ) (W : S → ℝ≥0∞) :
    bm_history M θ i n (fun s as => ∑ a ∈ M.A (s (Fin.last n)),
      θ.dist n s as a*bellmanQ M α W (s (Fin.last n)) a)=
      expCost M θ i n+(α : ℝ≥0∞)*expState M θ i (n+1) W := by
  rw [bm_expState_succ]
  change bm_history M θ i n (fun s as => ∑ a ∈ M.A (s (Fin.last n)),
      θ.dist n s as a*bellmanQ M α W (s (Fin.last n)) a)=
    bm_history M θ i n (fun s as => ∑ a ∈ M.A (s (Fin.last n)),
      θ.dist n s as a*(M.C (s (Fin.last n)) a : ℝ≥0∞))+
    (α : ℝ≥0∞)*bm_history M θ i n (fun s as => ∑ a ∈ M.A (s (Fin.last n)),
      θ.dist n s as a*∑' j, M.P (s (Fin.last n)) a j*W j)
  rw [← bm_history_add_mul]
  unfold bm_history
  apply tsum_congr
  intro s
  apply tsum_congr
  intro as
  congr 1
  dsimp only
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

lemma bm_hist_start_zero (M : MDC S Act) (θ : Policy M) (i : S) (n : ℕ)
    (s : Fin (n+1) → S) (as : Fin n → Act) (h : s 0 ≠ i) : histProb M θ i n s as=0 := by
  induction n with
  | zero => simp [histProb,h]
  | succ n ih =>
    have h' : Fin.init s 0 ≠ i := h
    simp only [histProb,ih (Fin.init s) (Fin.init as) h',zero_mul]

lemma bm_hist_start (M : MDC S Act) (θ : Policy M) (i : S) (n : ℕ)
    (s : Fin (n+1) → S) (as : Fin n → Act) (h : histProb M θ i n s as ≠ 0) : s 0=i := by
  by_contra hn
  exact h (bm_hist_start_zero M θ i n s as hn)

lemma bm_concentrated_action (M : MDC S Act) (θ : Policy M) (α : ℝ≥0)
    (h : ConcentratedOnOptActions M α θ) (i : S) (n : ℕ)
    (s : Fin (n+1) → S) (as : Fin n → Act) (hp : histProb M θ i n s as ≠ 0)
    (a : Act) (ha : θ.dist n s as a ≠ 0) : a ∈ optActions M α (s (Fin.last n)) := by
  cases n with
  | zero =>
    have hs : s=fun _ => s 0 := by
      funext k
      have hk : k=0 := Fin.eq_zero k
      exact congrArg s hk
    have has : as=fun k => Fin.elim0 k := Subsingleton.elim _ _
    rw [hs,has] at ha
    exact h.1 (s 0) a ha
  | succ n =>
    have hi := bm_hist_start M θ i (n+1) s as hp
    rw [← hi] at hp
    exact h.2 (n+1) (by omega) s as hp a ha

lemma bm_concentrated_stage (M : MDC S Act) (θ : Policy M) (α : ℝ≥0)
    (hα0 : 0 < α) (hα1 : α < 1) (h : ConcentratedOnOptActions M α θ) (i : S) (n : ℕ) :
    expState M θ i n (valueFn M α)=expCost M θ i n+
      (α : ℝ≥0∞)*expState M θ i (n+1) (valueFn M α) := by
  classical
  rw [← bm_policy_average]
  unfold expState bm_history
  apply tsum_congr
  intro s
  apply tsum_congr
  intro as
  dsimp only
  by_cases hp : histProb M θ i n s as=0
  · simp [hp]
  · congr 1
    symm
    calc
      _ = ∑ a ∈ M.A (s (Fin.last n)), θ.dist n s as a*valueFn M α (s (Fin.last n)) := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : θ.dist n s as a=0
        · simp [ha]
        · have hh := bm_concentrated_action M θ α h i n s as hp a ha
          have hQ := (Finset.mem_filter.mp hh).2
          rw [hQ,← bm_value_fixed M α hα0 hα1]
      _ = _ := by rw [← Finset.sum_mul,θ.dist_sum,one_mul]

lemma bm_concentrated_optimal (M : MDC S Act) (θ : Policy M) (α : ℝ≥0)
    (hα0 : 0 < α) (hα1 : α < 1) (h : ConcentratedOnOptActions M α θ) :
    IsDiscountOptimal M θ α := by
  have he (i : S) (n : ℕ) : finiteHorizonCost M θ α n i+
      (α : ℝ≥0∞)^n*expState M θ i n (valueFn M α)=valueFn M α i := by
    induction n with
    | zero => simp [finiteHorizonCost,Accepted.expState_zero]
    | succ n ih =>
      calc
        _ = finiteHorizonCost M θ α n i+(α : ℝ≥0∞)^n*
            (expCost M θ i n+(α : ℝ≥0∞)*expState M θ i (n+1) (valueFn M α)) := by
          simp only [finiteHorizonCost,Finset.sum_range_succ,pow_succ,mul_add,mul_assoc,add_assoc]
        _ = _ := by rw [← bm_concentrated_stage M θ α hα0 hα1 h i n,ih]
  intro i
  apply le_antisymm
  · rw [discountedCost,ENNReal.tsum_eq_iSup_nat]
    apply iSup_le
    intro n
    exact (le_self_add : finiteHorizonCost M θ α n i ≤ _).trans_eq (he i n)
  · exact iInf_le _ θ

lemma bm_tsum_eq_term {ι : Type*} (F G : ι → ℝ≥0∞) (h : ∀ j, F j ≤ G j)
    (hfinite : (∑' j, F j) ≠ ⊤) (he : (∑' j, F j)=∑' j, G j) (j : ι) : F j=G j := by
  by_contra hn
  have hlt := ENNReal.tsum_lt_tsum hfinite h (lt_of_le_of_ne (h j) hn)
  rw [he] at hlt
  exact (lt_irrefl _ hlt)

lemma bm_finset_eq_term {ι : Type*} (s : Finset ι) (F G : ι → ℝ≥0∞)
    (h : ∀ j ∈ s, F j ≤ G j) (hfinite : (∑ j ∈ s, F j) ≠ ⊤)
    (he : (∑ j ∈ s, F j)=∑ j ∈ s, G j) (j : ι) (hj : j ∈ s) : F j=G j := by
  classical
  have hF : (∑' j : {j // j ∈ s}, F j)=∑ j ∈ s, F j := by
    rw [tsum_fintype,Finset.sum_coe_sort]
  have hG : (∑' j : {j // j ∈ s}, G j)=∑ j ∈ s, G j := by
    rw [tsum_fintype,Finset.sum_coe_sort]
  exact bm_tsum_eq_term (fun j : {j // j ∈ s} => F j) (fun j => G j)
    (fun j => h j j.2) (hF ▸ hfinite) (by rw [hF,hG,he]) ⟨j,hj⟩

lemma bm_hist_le_one (M : MDC S Act) (θ : Policy M) (i : S) (n : ℕ)
    (s : Fin (n+1) → S) (as : Fin n → Act) : histProb M θ i n s as ≤ 1 := by
  calc
    _ = histProb M θ i n s as*1 := by rw [mul_one]
    _ ≤ ∑' as', histProb M θ i n s as'*1 := ENNReal.le_tsum as
    _ ≤ expState M θ i n (fun _ => 1) := ENNReal.le_tsum s
    _ = 1 := bm_expState_one M θ i n

lemma bm_optimal_stage (M : MDC S Act) (θ : Policy M) (α : ℝ≥0)
    (hα0 : 0 < α) (hα1 : α < 1) (hfinite : ∀ i, valueFn M α i ≠ ⊤)
    (hopt : IsDiscountOptimal M θ α) (i : S) (n : ℕ) :
    expState M θ i n (valueFn M α)=
      bm_history M θ i n (fun s as => ∑ a ∈ M.A (s (Fin.last n)),
        θ.dist n s as a*bellmanQ M α (valueFn M α) (s (Fin.last n)) a) ∧
      expState M θ i n (valueFn M α) ≠ ⊤ := by
  have he (k : ℕ) : finiteHorizonCost M θ α k i+(α : ℝ≥0∞)^k*
      expState M θ i k (valueFn M α)=valueFn M α i :=
    le_antisymm ((bm_prefix_value_le_cost M θ α hα0 hα1 i k).trans_eq (hopt i))
      (bm_value_le_prefix M θ α hα0 hα1 i k)
  have hpre : finiteHorizonCost M θ α n i ≠ ⊤ :=
    ne_of_lt (((le_self_add : finiteHorizonCost M θ α n i ≤ _).trans_eq (he n)).trans_lt
      (lt_top_iff_ne_top.mpr (hfinite i)))
  have ha0 : (α : ℝ≥0∞) ≠ 0 := by exact_mod_cast hα0.ne'
  have hp0 := pow_ne_zero n ha0
  have hptop : (α : ℝ≥0∞)^n ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hprod : (α : ℝ≥0∞)^n*expState M θ i n (valueFn M α) ≤ valueFn M α i :=
    (le_add_self).trans_eq (he n)
  have hstate : expState M θ i n (valueFn M α) ≠ ⊤ := by
    intro ht
    rw [ht,ENNReal.mul_top hp0] at hprod
    exact hfinite i (top_le_iff.mp hprod)
  refine ⟨?_,hstate⟩
  rw [bm_policy_average]
  apply (ENNReal.mul_right_inj hp0 hptop).mp
  apply (ENNReal.add_right_inj hpre).mp
  calc
    _ = valueFn M α i := he n
    _ = finiteHorizonCost M θ α (n+1) i+(α : ℝ≥0∞)^(n+1)*
        expState M θ i (n+1) (valueFn M α) := (he (n+1)).symm
    _ = _ := by
      simp only [finiteHorizonCost,Finset.sum_range_succ,pow_succ,mul_add,mul_assoc,add_assoc]

lemma bm_optimal_action (M : MDC S Act) (θ : Policy M) (α : ℝ≥0)
    (hα0 : 0 < α) (hα1 : α < 1) (hfinite : ∀ i, valueFn M α i ≠ ⊤)
    (hopt : IsDiscountOptimal M θ α) (i : S) (n : ℕ)
    (s : Fin (n+1) → S) (as : Fin n → Act) (hp : histProb M θ i n s as ≠ 0)
    (a : Act) (ha : θ.dist n s as a ≠ 0) : a ∈ optActions M α (s (Fin.last n)) := by
  classical
  have hmem : a ∈ M.A (s (Fin.last n)) := by
    by_contra hn
    exact ha (θ.dist_supp n s as a hn)
  let F := fun (s : Fin (n+1) → S) (as : Fin n → Act) =>
    histProb M θ i n s as*valueFn M α (s (Fin.last n))
  let G := fun (s : Fin (n+1) → S) (as : Fin n → Act) => histProb M θ i n s as*
    ∑ a ∈ M.A (s (Fin.last n)), θ.dist n s as a*bellmanQ M α (valueFn M α) (s (Fin.last n)) a
  have hFG : ∀ s as, F s as ≤ G s as := by
    intro s as
    apply mul_le_mul_right
    rw [bm_value_fixed M α hα0 hα1]
    exact bm_average_min M θ α _ n s as
  obtain ⟨hstage,hstate⟩ := bm_optimal_stage M θ α hα0 hα1 hfinite hopt i n
  have houter : (∑' as, F s as)=∑' as, G s as :=
    bm_tsum_eq_term (fun s => ∑' as, F s as) (fun s => ∑' as, G s as)
      (fun s => ENNReal.tsum_le_tsum (hFG s)) hstate hstage s
  have hinnerfinite : (∑' as, F s as) ≠ ⊤ :=
    ne_of_lt ((ENNReal.le_tsum s).trans_lt (lt_top_iff_ne_top.mpr hstate))
  have hterm := bm_tsum_eq_term (F s) (G s) (hFG s) hinnerfinite houter as
  have hpfinite : histProb M θ i n s as ≠ ⊤ :=
    ne_of_lt ((bm_hist_le_one M θ i n s as).trans_lt ENNReal.one_lt_top)
  have havg : valueFn M α (s (Fin.last n))=
      ∑ b ∈ M.A (s (Fin.last n)), θ.dist n s as b*
        bellmanQ M α (valueFn M α) (s (Fin.last n)) b :=
    (ENNReal.mul_right_inj hp hpfinite).mp hterm
  have hconst : (∑ b ∈ M.A (s (Fin.last n)), θ.dist n s as b*valueFn M α (s (Fin.last n)))=
      valueFn M α (s (Fin.last n)) := by rw [← Finset.sum_mul,θ.dist_sum,one_mul]
  have haction := bm_finset_eq_term (M.A (s (Fin.last n)))
    (fun b => θ.dist n s as b*valueFn M α (s (Fin.last n)))
    (fun b => θ.dist n s as b*bellmanQ M α (valueFn M α) (s (Fin.last n)) b)
    (by
      intro b hb
      apply mul_le_mul_right
      rw [bm_value_fixed M α hα0 hα1]
      exact Finset.inf'_le _ hb)
    (by rw [hconst]; exact hfinite _) (hconst.trans havg) a hmem
  have hafinite : θ.dist n s as a ≠ ⊤ := by
    have hd : θ.dist n s as a ≤ 1 := by
      calc
        _ ≤ ∑ b ∈ M.A (s (Fin.last n)), θ.dist n s as b := Finset.single_le_sum (fun _ _ => bot_le) hmem
        _ = 1 := θ.dist_sum n s as
    exact ne_of_lt (hd.trans_lt ENNReal.one_lt_top)
  have heq := (ENNReal.mul_right_inj ha hafinite).mp haction
  apply Finset.mem_filter.mpr
  exact ⟨hmem,heq.symm.trans (bm_value_fixed M α hα0 hα1 _)⟩

lemma bm_policy_characterization (M : MDC S Act) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1)
    (θ : Policy M) :
    (ConcentratedOnOptActions M α θ → IsDiscountOptimal M θ α) ∧
      ((∀ i : S, valueFn M α i ≠ ⊤) → IsDiscountOptimal M θ α → ConcentratedOnOptActions M α θ) := by
  refine ⟨bm_concentrated_optimal M θ α hα0 hα1,?_⟩
  intro hfinite hopt
  refine ⟨?_,?_⟩
  · intro i a ha
    exact bm_optimal_action M θ α hα0 hα1 hfinite hopt i 0 (fun _ => i)
      (fun k => Fin.elim0 k) (by simp [histProb]) a ha
  · intro n _ s as hp a ha
    exact bm_optimal_action M θ α hα0 hα1 hfinite hopt (s 0) n s as hp a ha

end
end SennottDP.Discounted

open SennottDP.Discounted

/-- Sennott (1999), Proposition 4.4.1, pp. 67–69: a policy `θ` for the infinite horizon is
optimal for the expected `α`-discounted cost criterion if and only if (i) for each initial state
`i` the distribution `θ(a | i)` is concentrated on `B_i(α)`, and (ii) for `n ≥ 1`, if `h_n` is a
history under `θ` with state `i_n`, then `θ(a | h_n)` is concentrated on `B_{i_n}(α)`.
Sufficiency is stated as in the book. Necessity is stated under the additional hypothesis that
`V_α` is finite: the book's necessity argument ("both inequalities in (4.10) must be
equalities") needs `V_α(i) < ∞`, and without it the necessity claim fails (a policy may act
suboptimally after reaching a finite-value state from an initial state with `V_α = ∞`). -/
theorem solution {S : Type} [Countable S] {Act : Type} (M : MDC S Act)
    (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1) (θ : Policy M) :
    (ConcentratedOnOptActions M α θ → IsDiscountOptimal M θ α) ∧
      ((∀ i : S, valueFn M α i ≠ ⊤) →
        IsDiscountOptimal M θ α → ConcentratedOnOptActions M α θ) := by
  exact bm_policy_characterization M α hα0 hα1 θ

#print axioms solution

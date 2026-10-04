-- Prove2me | solution 1 for SennottDP.AvgFinite.prop_4_5_4_monotone_left_continuous
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T01:31:21.875999+00:00
-- url     : https://prove2.me/submissions/7466d6a1-d933-4c8c-ba88-4812af86b09e

import Definitions.Def_SennottDP_AvgFinite_Criteria
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000




open scoped ENNReal NNReal
open Classical

namespace SennottDP.BlackwellFH

/-- A Markov decision chain `Δ` (Sennott, §2.1, pp. 15–16): for each state `i` a finite nonempty
action set `A i`, a nonnegative finite cost `C i a`, and for each `a ∈ A i` a transition
probability distribution `P i a ·` on the state space (`∑_j P_ij(a) = 1`). The state space is
countable wherever it is used (`[Countable S]` on the theorems). -/
structure MDC (S : Type*) (Act : Type*) where
  A : S → Finset Act
  A_nonempty : ∀ i, (A i).Nonempty
  C : S → Act → ℝ≥0
  P : S → Act → S → ℝ≥0∞
  P_sum : ∀ i, ∀ a ∈ A i, ∑' j, P i a j = 1

namespace MDC

variable {S Act : Type*} (M : MDC S Act)

/-- A general (history-dependent, randomized) policy `θ` (§2.2, pp. 20–22). A history at time `t`
is `h_t = (i_0, a_0, …, i_{t-1}, a_{t-1}, i_t)`; it is encoded as the list of the past
state–action pairs, **most recent first**, `[(i_{t-1}, a_{t-1}), …, (i_0, a_0)]`, together with
the current state `i_t`. `σ h i a` is the probability `θ(a | h_t)` of choosing action `a`; it is a
probability distribution on `A i`. A policy for the `n` horizon (p. 22) is the restriction of such
a policy to the decisions at `t = 0, …, n − 1`. -/
structure Policy where
  σ : List (S × Act) → S → Act → ℝ≥0∞
  σ_sum : ∀ h i, ∑ a ∈ M.A i, σ h i a = 1
  σ_supp : ∀ h i a, a ∉ M.A i → σ h i a = 0

/-- A stationary policy `f` (p. 20): a distinguished action `f i ∈ A i` for every state `i`. -/
def Stationary := {f : S → Act // ∀ i, f i ∈ M.A i}

variable {M}

/-- The deterministic Markov policy `(g 0, g 1, g 2, …)` (p. 21): at time `t`, in state `i`, it
chooses the action `(g t) i` with probability one. The time `t` is the length of the history. -/
noncomputable def Policy.ofMarkov (g : ℕ → M.Stationary) : M.Policy where
  σ h i a := if a = (g h.length).1 i then 1 else 0
  σ_sum h i := by simp [(g h.length).2 i]
  σ_supp h i a ha := by
    have : a ≠ (g h.length).1 i := fun e => ha (e ▸ (g h.length).2 i)
    simp [this]

/-- The continuation policy `ψ(i, a, ·)` of `θ` after the initial state `i` and the initial action
`a` (proof of Theorem 3.1.2, p. 38): it is the rule `θ` uses from time `t = 1` on, re-indexed so
that `t = 1` becomes time `0`. A history `(j, a_1, …, i_s)` of the continuation is the history
`(i, a, j, a_1, …, i_s)` of `θ`; with most-recent-first lists this appends `(i, a)` at the end. -/
noncomputable def Policy.shift (θ : M.Policy) (i : S) (a : Act) : M.Policy where
  σ h k b := θ.σ (h ++ [(i, a)]) k b
  σ_sum _ k := θ.σ_sum _ k
  σ_supp _ k b hb := θ.σ_supp _ k b hb

/-- `histProb θ i t h j` is the probability, under `θ` and initial state `X_0 = i`, that the history
at time `t` is `(h, j)` — past pairs `h` (most recent first, of length `t`) and current state
`X_t = j` (§2.3, pp. 22–23):
`P_θ(h_t) = ∏_{s<t} θ(a_s | h_s) P_{i_s i_{s+1}}(a_s)`. -/
noncomputable def histProb (θ : M.Policy) (i : S) : ℕ → List (S × Act) → S → ℝ≥0∞
  | 0, [], j => if j = i then 1 else 0
  | 0, _ :: _, _ => 0
  | _ + 1, [], _ => 0
  | t + 1, (k, a) :: h, j => histProb θ i t h k * θ.σ h k a * M.P k a j

/-- `f` is a limit point of the sequence `(f_r)` of stationary policies for `Δ` (Definition B.1,
pp. 288–289): there is a subsequence `f_{r_k}` such that for each state `i`,
`f_{r_k}(i) = f(i)` for all sufficiently large `k`. -/
def IsLimitPoint (fs : ℕ → M.Stationary) (f : M.Stationary) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, ∀ᶠ k in Filter.atTop, (fs (φ k)).1 i = f.1 i

end MDC

end SennottDP.BlackwellFH


open scoped ENNReal NNReal
open Classical

namespace SennottDP.BlackwellFH

namespace MDC

variable {S Act : Type*} {M : MDC S Act}

/-- `P_θ(X_t = j, A_t = a | X_0 = i)`, the joint law of the state and the action at time `t`
(§2.3, pp. 22–23): the sum, over all histories `h_t` ending in `j`, of `P_θ(h_t) θ(a | h_t)`. -/
noncomputable def stateActionProb (θ : M.Policy) (i : S) (t : ℕ) (j : S) (a : Act) : ℝ≥0∞ :=
  ∑' h : List (S × Act), histProb θ i t h j * θ.σ h j a

/-- `P_θ(X_t = j | X_0 = i)`, the law of the state at time `t`. -/
noncomputable def stateProb (θ : M.Policy) (i : S) (t : ℕ) (j : S) : ℝ≥0∞ :=
  ∑' h : List (S × Act), histProb θ i t h j

/-- The statistical average cost at time `t`, equation (2.6), p. 23:
`E_θ[C(X_t, A_t) | X_0 = i] = ∑_j ∑_{a ∈ A_j} C(j, a) P_θ(X_t = j, A_t = a | X_0 = i)`. -/
noncomputable def expectedCost (θ : M.Policy) (i : S) (t : ℕ) : ℝ≥0∞ :=
  ∑' j : S, ∑ a ∈ M.A j, (M.C j a : ℝ≥0∞) * stateActionProb θ i t j a

/-- The expected terminal cost `E_θ[F(X_t) | X_0 = i] = ∑_j F(j) P_θ(X_t = j | X_0 = i)`. -/
noncomputable def expectedTerminal (F : S → ℝ≥0) (θ : M.Policy) (i : S) (t : ℕ) : ℝ≥0∞ :=
  ∑' j : S, (F j : ℝ≥0∞) * stateProb θ i t j

/-- The `n` horizon expected discounted cost under `θ` with terminal cost `F`, equation (2.9),
p. 25: `v_{θ,α,n}(i) = ∑_{t=0}^{n-1} α^t E_θ[C(X_t,A_t) | X_0 = i] + α^n E_θ[F(X_n) | X_0 = i]`,
with values in `[0, ∞]` (Remark 2.4.2). For `n = 0` it is `F(i)`. -/
noncomputable def horizonCost (F : S → ℝ≥0) (α : ℝ≥0) (θ : M.Policy) (n : ℕ) (i : S) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range n, (α : ℝ≥0∞) ^ t * expectedCost θ i t
    + (α : ℝ≥0∞) ^ n * expectedTerminal F θ i n

variable (M)

/-- The `n` horizon expected discounted value function, equation (2.10), p. 25:
`v_{α,n}(i) = inf_θ v_{θ,α,n}(i)`, the infimum over all general policies, in `[0, ∞]`. -/
noncomputable def value (F : S → ℝ≥0) (α : ℝ≥0) (n : ℕ) (i : S) : ℝ≥0∞ :=
  ⨅ θ : M.Policy, horizonCost F α θ n i

/-- Definition 2.4.1, p. 25: `θ` is optimal for the `n` horizon if `v_{θ,α,n}(i) = v_{α,n}(i)`
for every state `i`. -/
def IsOptimal (F : S → ℝ≥0) (α : ℝ≥0) (n : ℕ) (θ : M.Policy) : Prop :=
  ∀ i, horizonCost F α θ n i = M.value F α n i

/-- The auxiliary function (3.1), p. 36, for `n ≥ 1`:
`u_{α,n}(i, a) = C(i, a) + α ∑_j P_ij(a) v_{α,n-1}(j)`. (It is only used with `n ≥ 1`.) -/
noncomputable def aux (F : S → ℝ≥0) (α : ℝ≥0) (n : ℕ) (i : S) (a : Act) : ℝ≥0∞ :=
  (M.C i a : ℝ≥0∞) + (α : ℝ≥0∞) * ∑' j, M.P i a j * M.value F α (n - 1) j

/-- The set of minimizing actions, p. 36:
`B_i(α, n) = {b ∈ A_i | u_{α,n}(i, b) = min_{a ∈ A_i} u_{α,n}(i, a)}`. -/
noncomputable def minSet (F : S → ℝ≥0) (α : ℝ≥0) (n : ℕ) (i : S) : Finset Act :=
  (M.A i).filter
    (fun b => M.aux F α n i b = (M.A i).inf' (M.A_nonempty i) (M.aux F α n i))

end MDC

end SennottDP.BlackwellFH




namespace SennottDP.BlackwellFH
open scoped ENNReal NNReal
open Filter Topology
noncomputable section
variable {S Act : Type*}

def fa_listEquiv (β : Type*) : List β ≃ Unit ⊕ (β × List β) where
  toFun
    | [] => Sum.inl ()
    | b :: h => Sum.inr (b,h)
  invFun
    | Sum.inl _ => []
    | Sum.inr (b,h) => b :: h
  left_inv h := by cases h <;> rfl
  right_inv h := by
    cases h with
    | inl u => cases u; rfl
    | inr p => cases p; rfl

lemma fa_tsum_list {β : Type*} (F : List β → ℝ≥0∞) :
    (∑' h, F h)=F []+∑' b, ∑' h, F (b::h) := by
  rw [← (fa_listEquiv β).symm.tsum_eq]
  rw [ENNReal.summable.tsum_sum ENNReal.summable]
  change (∑' u : Unit, F [])+(∑' p : β × List β, F (p.1::p.2))=F []+∑' b, ∑' h, F (b::h)
  rw [ENNReal.tsum_prod',tsum_eq_single ()]
  intro u hu
  exact False.elim (hu (Subsingleton.elim u ()))

def fa_expect (M : MDC S Act) (θ : M.Policy) (i : S) (t : ℕ) (W : S → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' h, ∑' j, MDC.histProb θ i t h j*W j

lemma fa_history_length (M : MDC S Act) (θ : M.Policy) (i : S) (t : ℕ)
    (h : List (S × Act)) (j : S) (hne : h.length ≠ t) : MDC.histProb θ i t h j=0 := by
  induction t generalizing h j with
  | zero => cases h <;> simp_all [MDC.histProb]
  | succ t ih =>
    cases h with
    | nil => rfl
    | cons p h =>
      have hn : h.length ≠ t := by simpa using hne
      simp [MDC.histProb,ih h p.1 hn]

lemma fa_expect_zero (M : MDC S Act) (θ : M.Policy) (i : S) (W : S → ℝ≥0∞) :
    fa_expect M θ i 0 W=W i := by
  classical
  unfold fa_expect
  rw [fa_tsum_list]
  simp only [MDC.histProb,zero_mul,tsum_zero,add_zero]
  rw [tsum_eq_single i]
  · simp
  · intro j hj
    simp [hj]

lemma fa_expect_succ (M : MDC S Act) (θ : M.Policy) (i : S) (t : ℕ) (W : S → ℝ≥0∞) :
    fa_expect M θ i (t+1) W=
      ∑' h : List (S × Act), ∑' j : S, MDC.histProb θ i t h j*
        ∑ a ∈ M.A j, θ.σ h j a*∑' k, M.P j a k*W k := by
  classical
  unfold fa_expect
  rw [fa_tsum_list]
  simp only [MDC.histProb,zero_mul,tsum_zero,zero_add]
  rw [ENNReal.tsum_prod']
  calc
    _ = ∑' j : S, ∑' h : List (S × Act), ∑' a : Act, ∑' k : S,
        MDC.histProb θ i t h j*θ.σ h j a*M.P j a k*W k := by
      apply tsum_congr
      intro j
      rw [ENNReal.tsum_comm]
    _ = ∑' h : List (S × Act), ∑' j : S, ∑' a : Act, ∑' k : S,
        MDC.histProb θ i t h j*θ.σ h j a*M.P j a k*W k := ENNReal.tsum_comm
    _ = _ := by
      refine tsum_congr (fun h => tsum_congr (fun j => ?_))
      have he : (∑' a : Act, ∑' k : S, MDC.histProb θ i t h j*θ.σ h j a*M.P j a k*W k)=
          MDC.histProb θ i t h j*∑' a : Act, θ.σ h j a*∑' k : S, M.P j a k*W k := by
        simp_rw [mul_assoc,ENNReal.tsum_mul_left]
      rw [he]
      congr 1
      apply tsum_eq_sum
      intro a ha
      simp [θ.σ_supp h j a ha]

lemma fa_expect_add_mul (M : MDC S Act) (θ : M.Policy) (i : S) (t : ℕ)
    (U W : S → ℝ≥0∞) (c : ℝ≥0∞) :
    fa_expect M θ i t (fun j => U j+c*W j)=fa_expect M θ i t U+c*fa_expect M θ i t W := by
  unfold fa_expect
  rw [← ENNReal.tsum_mul_left,← ENNReal.tsum_add]
  refine tsum_congr (fun h => ?_)
  rw [← ENNReal.tsum_mul_left,← ENNReal.tsum_add]
  refine tsum_congr (fun j => ?_)
  ring

lemma fa_expectedTerminal (M : MDC S Act) (F : S → ℝ≥0) (θ : M.Policy) (i : S) (t : ℕ) :
    MDC.expectedTerminal F θ i t=fa_expect M θ i t (fun j => (F j : ℝ≥0∞)) := by
  unfold MDC.expectedTerminal MDC.stateProb fa_expect
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro h
  apply tsum_congr
  intro j
  ring

lemma fa_expectedCost (M : MDC S Act) (θ : M.Policy) (i : S) (t : ℕ) :
    MDC.expectedCost θ i t=∑' h : List (S × Act), ∑' j : S,
      MDC.histProb θ i t h j*∑ a ∈ M.A j, θ.σ h j a*(M.C j a : ℝ≥0∞) := by
  classical
  unfold MDC.expectedCost MDC.stateActionProb
  simp_rw [← ENNReal.tsum_mul_left]
  have hs (j : S) : (∑ a ∈ M.A j, ∑' h : List (S × Act),
      (M.C j a : ℝ≥0∞)*(MDC.histProb θ i t h j*θ.σ h j a))=
      ∑' h : List (S × Act), ∑ a ∈ M.A j,
        (M.C j a : ℝ≥0∞)*(MDC.histProb θ i t h j*θ.σ h j a) := by
    exact (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm
  simp_rw [hs]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro h
  apply tsum_congr
  intro j
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

end
end SennottDP.BlackwellFH



namespace SennottDP.BlackwellFH
open scoped ENNReal NNReal
open Classical Filter Topology
noncomputable section
variable {S Act : Type*}

def fa_reverseEquiv (β : Type*) : List β ≃ List β where
  toFun := List.reverse
  invFun := List.reverse
  left_inv := List.reverse_reverse
  right_inv := List.reverse_reverse

lemma fa_tsum_append {β : Type*} (F : List β → ℝ≥0∞) :
    (∑' h, F h)=F []+∑' b, ∑' h, F (h++[b]) := by
  rw [← (fa_reverseEquiv β).tsum_eq]
  change (∑' h : List β, F h.reverse)= _
  rw [fa_tsum_list]
  simp only [List.reverse_nil,List.reverse_cons]
  congr 1
  apply tsum_congr
  intro b
  exact (fa_reverseEquiv β).tsum_eq (fun h => F (h++[b]))

lemma fa_hist_append (M : MDC S Act) (θ : M.Policy) (i k : S) (a : Act) (t : ℕ)
    (h : List (S × Act)) (j : S) :
    MDC.histProb θ i (t+1) (h++[(k,a)]) j=
      (if k=i then 1 else 0)*θ.σ [] k a*
        ∑' l : S, M.P k a l*MDC.histProb (θ.shift k a) l t h j := by
  classical
  induction t generalizing h j with
  | zero =>
    cases h with
    | nil => simp [MDC.histProb,eq_comm]
    | cons p h => cases h <;> simp [MDC.histProb]
  | succ t ih =>
    cases h with
    | nil => simp [MDC.histProb]
    | cons p h =>
      simp only [List.cons_append,MDC.histProb]
      rw [ih]
      simp only [MDC.Policy.shift]
      simp_rw [← ENNReal.tsum_mul_left,← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro l
      ring

lemma fa_first_step_expect (M : MDC S Act) (θ : M.Policy) (i : S) (t : ℕ)
    (F : List (S × Act) → S → ℝ≥0∞) :
    (∑' h : List (S × Act), ∑' j : S, MDC.histProb θ i (t+1) h j*F h j)=
      ∑ a ∈ M.A i, θ.σ [] i a*∑' k : S, M.P i a k*
        ∑' h : List (S × Act), ∑' j : S, MDC.histProb (θ.shift i a) k t h j*F (h++[(i,a)]) j := by
  classical
  rw [fa_tsum_append]
  simp only [MDC.histProb,zero_mul,tsum_zero,zero_add]
  rw [ENNReal.tsum_prod']
  have he (k : S) : (∑' a : Act, ∑' h : List (S × Act), ∑' j : S,
      MDC.histProb θ i (t+1) (h++[(k,a)]) j*F (h++[(k,a)]) j)=
      (if k=i then 1 else 0)*∑' a : Act, θ.σ [] k a*∑' l : S, M.P k a l*
        ∑' h : List (S × Act), ∑' j : S,
          MDC.histProb (θ.shift k a) l t h j*F (h++[(k,a)]) j := by
    simp_rw [fa_hist_append]
    calc
      _ = ∑' a : Act, ∑' h : List (S × Act), ∑' j : S, ∑' l : S,
          (if k=i then 1 else 0)*θ.σ [] k a*M.P k a l*
            MDC.histProb (θ.shift k a) l t h j*F (h++[(k,a)]) j := by
        refine tsum_congr (fun a => tsum_congr (fun h => tsum_congr (fun j => ?_)))
        rw [← ENNReal.tsum_mul_left,← ENNReal.tsum_mul_right]
        refine tsum_congr (fun l => ?_)
        ring
      _ = ∑' a : Act, ∑' h : List (S × Act), ∑' l : S, ∑' j : S,
          (if k=i then 1 else 0)*θ.σ [] k a*M.P k a l*
            MDC.histProb (θ.shift k a) l t h j*F (h++[(k,a)]) j := by
        refine tsum_congr (fun a => tsum_congr (fun h => ?_))
        rw [ENNReal.tsum_comm]
      _ = ∑' a : Act, ∑' l : S, ∑' h : List (S × Act), ∑' j : S,
          (if k=i then 1 else 0)*θ.σ [] k a*M.P k a l*
            MDC.histProb (θ.shift k a) l t h j*F (h++[(k,a)]) j := by
        refine tsum_congr (fun a => ?_)
        rw [ENNReal.tsum_comm]
      _ = _ := by
        simp_rw [← ENNReal.tsum_mul_left]
        refine tsum_congr (fun a => tsum_congr (fun l => tsum_congr (fun h => tsum_congr (fun j => ?_))))
        ring
  simp_rw [he]
  rw [tsum_eq_single i]
  · simp only [ite_true,one_mul]
    apply tsum_eq_sum
    intro a ha
    simp [θ.σ_supp [] i a ha]
  · intro k hk
    simp [hk]

end
end SennottDP.BlackwellFH



namespace SennottDP.BlackwellFH
open scoped ENNReal NNReal
open Filter Topology
noncomputable section
variable {S Act : Type*}

def fa_Q (M : MDC S Act) (α : ℝ≥0) (W : S → ℝ≥0∞) (i : S) (a : Act) : ℝ≥0∞ :=
  (M.C i a : ℝ≥0∞)+(α : ℝ≥0∞)*∑' j, M.P i a j*W j

def fa_T (M : MDC S Act) (α : ℝ≥0) (W : S → ℝ≥0∞) (i : S) : ℝ≥0∞ :=
  (M.A i).inf' (M.A_nonempty i) (fa_Q M α W i)

def fa_iter (M : MDC S Act) (F : S → ℝ≥0) (α : ℝ≥0) : ℕ → S → ℝ≥0∞
  | 0 => fun i => F i
  | n+1 => fa_T M α (fa_iter M F α n)

lemma fa_selector (M : MDC S Act) (α : ℝ≥0) (W : S → ℝ≥0∞) :
    ∃ f : M.Stationary, ∀ i, fa_Q M α W i (f.1 i)=fa_T M α W i := by
  classical
  have h : ∀ i, ∃ a ∈ M.A i, fa_Q M α W i a=fa_T M α W i := by
    intro i
    obtain ⟨a,ha,he⟩ := Finset.exists_mem_eq_inf' (M.A_nonempty i) (fa_Q M α W i)
    exact ⟨a,ha,he.symm⟩
  choose f hf he using h
  exact ⟨⟨f,hf⟩,he⟩

lemma fa_average_min (M : MDC S Act) (θ : M.Policy) (α : ℝ≥0) (W : S → ℝ≥0∞)
    (h : List (S × Act)) (j : S) :
    fa_T M α W j ≤ ∑ a ∈ M.A j, θ.σ h j a*fa_Q M α W j a := by
  have he : (∑ a ∈ M.A j, θ.σ h j a*fa_T M α W j)=fa_T M α W j := by
    rw [← Finset.sum_mul,θ.σ_sum,one_mul]
  rw [← he]
  apply Finset.sum_le_sum
  intro a ha
  exact mul_le_mul_right (Finset.inf'_le (fa_Q M α W j) ha) (θ.σ h j a)

lemma fa_average_expect (M : MDC S Act) (θ : M.Policy) (α : ℝ≥0) (W : S → ℝ≥0∞)
    (i : S) (t : ℕ) :
    (∑' h : List (S × Act), ∑' j : S, MDC.histProb θ i t h j*
      ∑ a ∈ M.A j, θ.σ h j a*fa_Q M α W j a)=
      MDC.expectedCost θ i t+(α : ℝ≥0∞)*fa_expect M θ i (t+1) W := by
  rw [fa_expectedCost,fa_expect_succ,← ENNReal.tsum_mul_left,← ENNReal.tsum_add]
  apply tsum_congr
  intro h
  rw [← ENNReal.tsum_mul_left,← ENNReal.tsum_add]
  apply tsum_congr
  intro j
  rw [mul_left_comm (α : ℝ≥0∞) (MDC.histProb θ i t h j)]
  rw [← mul_add]
  congr 1
  simp only [fa_Q,mul_add,Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma fa_stage_le (M : MDC S Act) (θ : M.Policy) (α : ℝ≥0) (U W : S → ℝ≥0∞)
    (i : S) (t : ℕ) (h : ∀ h j, U j ≤ ∑ a ∈ M.A j, θ.σ h j a*fa_Q M α W j a) :
    fa_expect M θ i t U ≤ MDC.expectedCost θ i t+(α : ℝ≥0∞)*fa_expect M θ i (t+1) W := by
  rw [← fa_average_expect]
  exact ENNReal.tsum_le_tsum (fun h' => ENNReal.tsum_le_tsum
    (fun j => mul_le_mul_right (h h' j) (MDC.histProb θ i t h' j)))

lemma fa_stage_eq (M : MDC S Act) (θ : M.Policy) (α : ℝ≥0) (U W : S → ℝ≥0∞)
    (i : S) (t : ℕ) (h : ∀ h j, MDC.histProb θ i t h j ≠ 0 →
      U j = ∑ a ∈ M.A j, θ.σ h j a*fa_Q M α W j a) :
    fa_expect M θ i t U = MDC.expectedCost θ i t+(α : ℝ≥0∞)*fa_expect M θ i (t+1) W := by
  rw [← fa_average_expect]
  unfold fa_expect
  apply tsum_congr
  intro h'
  apply tsum_congr
  intro j
  by_cases hp : MDC.histProb θ i t h' j=0
  · simp [hp]
  · rw [h h' j hp]

def fa_prefix (M : MDC S Act) (θ : M.Policy) (α : ℝ≥0) (n : ℕ) (i : S) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range n, (α : ℝ≥0∞)^t*MDC.expectedCost θ i t

lemma fa_iter_lower (M : MDC S Act) (F : S → ℝ≥0) (θ : M.Policy) (α : ℝ≥0)
    (N : ℕ) (i : S) (k : ℕ) (hk : k ≤ N) :
    fa_iter M F α N i ≤ fa_prefix M θ α k i+(α : ℝ≥0∞)^k*
      fa_expect M θ i k (fa_iter M F α (N-k)) := by
  induction k with
  | zero => simp [fa_prefix,fa_expect_zero]
  | succ k ih =>
    have hNk : N-k=N-(k+1)+1 := by omega
    have hh := fa_stage_le M θ α (fa_iter M F α (N-k)) (fa_iter M F α (N-(k+1))) i k (by
      rw [hNk]
      exact fa_average_min M θ α _)
    calc
      _ ≤ fa_prefix M θ α k i+(α : ℝ≥0∞)^k*fa_expect M θ i k (fa_iter M F α (N-k)) := ih (by omega)
      _ ≤ fa_prefix M θ α k i+(α : ℝ≥0∞)^k*
          (MDC.expectedCost θ i k+(α : ℝ≥0∞)*fa_expect M θ i (k+1) (fa_iter M F α (N-(k+1)))) := by gcongr
      _ = _ := by
        simp only [fa_prefix,Finset.sum_range_succ,pow_succ,mul_add,mul_assoc,add_assoc]

lemma fa_iter_le_cost (M : MDC S Act) (F : S → ℝ≥0) (θ : M.Policy) (α : ℝ≥0) (N : ℕ) (i : S) :
    fa_iter M F α N i ≤ MDC.horizonCost F α θ N i := by
  have h := fa_iter_lower M F θ α N i N le_rfl
  simpa only [Nat.sub_self,fa_iter,← fa_expectedTerminal,fa_prefix,MDC.horizonCost] using h

lemma fa_markov_stage (M : MDC S Act) (g : ℕ → M.Stationary) (α : ℝ≥0) (W : S → ℝ≥0∞)
    (i : S) (t : ℕ) (h : List (S × Act)) (j : S)
    (hp : MDC.histProb (MDC.Policy.ofMarkov g) i t h j ≠ 0) :
    (∑ a ∈ M.A j, (MDC.Policy.ofMarkov g).σ h j a*fa_Q M α W j a)=
      fa_Q M α W j ((g t).1 j) := by
  classical
  have hlen : h.length=t := by
    by_contra hn
    exact hp (fa_history_length M _ i t h j hn)
  simp [MDC.Policy.ofMarkov,hlen,(g t).2 j]

lemma fa_markov_equal (M : MDC S Act) (F : S → ℝ≥0) (g : ℕ → M.Stationary) (α : ℝ≥0)
    (N : ℕ) (hg : ∀ t, t < N → ∀ j, fa_Q M α (fa_iter M F α (N-t-1)) j ((g t).1 j)=
      fa_iter M F α (N-t) j) (i : S) :
    MDC.horizonCost F α (MDC.Policy.ofMarkov g) N i=fa_iter M F α N i := by
  let θ := MDC.Policy.ofMarkov g
  have he (k : ℕ) (hk : k ≤ N) :
      fa_prefix M θ α k i+(α : ℝ≥0∞)^k*fa_expect M θ i k (fa_iter M F α (N-k))=
        fa_iter M F α N i := by
    induction k with
    | zero => simp [fa_prefix,fa_expect_zero]
    | succ k ih =>
      have hh := fa_stage_eq M θ α (fa_iter M F α (N-k)) (fa_iter M F α (N-(k+1))) i k (by
        intro h j hp
        rw [fa_markov_stage M g α _ i k h j hp]
        have hn : N-(k+1)=N-k-1 := by omega
        rw [hn]
        exact (hg k (by omega) j).symm)
      calc
        _ = fa_prefix M θ α k i+(α : ℝ≥0∞)^k*
            (MDC.expectedCost θ i k+(α : ℝ≥0∞)*fa_expect M θ i (k+1) (fa_iter M F α (N-(k+1)))) := by
          simp only [fa_prefix,Finset.sum_range_succ,pow_succ,mul_add,mul_assoc,add_assoc]
        _ = _ := by rw [← hh]; exact ih (by omega)
  simpa only [Nat.sub_self,fa_iter,← fa_expectedTerminal,fa_prefix,MDC.horizonCost] using he N le_rfl

lemma fa_attainment (M : MDC S Act) (F : S → ℝ≥0) (α : ℝ≥0) (N : ℕ) :
    ∃ θ : M.Policy, ∀ i, MDC.horizonCost F α θ N i=fa_iter M F α N i := by
  classical
  choose fs hfs using (fun n : ℕ => fa_selector M α (fa_iter M F α n))
  let g := fun t => fs (N-t-1)
  refine ⟨MDC.Policy.ofMarkov g,fun i => fa_markov_equal M F g α N ?_ i⟩
  intro t ht j
  have hn : N-t=(N-t-1)+1 := by omega
  rw [hn]
  exact hfs (N-t-1) j

lemma fa_value_eq (M : MDC S Act) (F : S → ℝ≥0) (α : ℝ≥0) (N : ℕ) :
    M.value F α N=fa_iter M F α N := by
  obtain ⟨θ,hθ⟩ := fa_attainment M F α N
  funext i
  exact le_antisymm ((iInf_le _ θ).trans_eq (hθ i)) (le_iInf (fun θ => fa_iter_le_cost M F θ α N i))

lemma fa_optimality_rec (M : MDC S Act) (F : S → ℝ≥0) (α : ℝ≥0) (n : ℕ) (hn : 1 ≤ n) (i : S) :
    M.value F α n i=(M.A i).inf' (M.A_nonempty i) (M.aux F α n i) := by
  have he : n=(n-1)+1 := by omega
  rw [fa_value_eq,he]
  change fa_T M α (fa_iter M F α (n-1)) i= _
  unfold MDC.aux
  rw [fa_value_eq]
  simp only [Nat.add_sub_cancel]
  rfl

lemma fa_markov_optimal (M : MDC S Act) (F : S → ℝ≥0) (α : ℝ≥0) (n : ℕ) (hn : 1 ≤ n)
    (f : ℕ → M.Stationary) (hf : ∀ t, t ≤ n-1 → ∀ i, (f (n-t)).1 i ∈ M.minSet F α (n-t) i) :
    M.IsOptimal F α n (MDC.Policy.ofMarkov (fun t => f (n-t))) := by
  intro i
  rw [fa_value_eq]
  apply fa_markov_equal
  intro t ht j
  have hm := (Finset.mem_filter.mp (hf t (by omega) j)).2
  have he := fa_optimality_rec M F α (n-t) (by omega) j
  rw [← he] at hm
  unfold MDC.aux at hm
  rw [fa_value_eq,fa_value_eq] at hm
  exact hm

end
end SennottDP.BlackwellFH



namespace SennottDP.BlackwellFH
open scoped ENNReal NNReal
open Classical Filter Topology
noncomputable section
variable {S Act : Type*}

def fa_initialAvg (M : MDC S Act) (θ : M.Policy) (i : S) (U : Act → S → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ a ∈ M.A i, θ.σ [] i a*∑' j, M.P i a j*U a j

lemma fa_initialAvg_add (M : MDC S Act) (θ : M.Policy) (i : S) (U W : Act → S → ℝ≥0∞) :
    fa_initialAvg M θ i (fun a j => U a j+W a j)=fa_initialAvg M θ i U+fa_initialAvg M θ i W := by
  simp only [fa_initialAvg,mul_add,ENNReal.tsum_add,Finset.sum_add_distrib]

lemma fa_initialAvg_mul (M : MDC S Act) (θ : M.Policy) (i : S) (c : ℝ≥0∞) (U : Act → S → ℝ≥0∞) :
    fa_initialAvg M θ i (fun a j => c*U a j)=c*fa_initialAvg M θ i U := by
  unfold fa_initialAvg
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro j
  ring

lemma fa_initialAvg_sum {ι : Type*} (M : MDC S Act) (θ : M.Policy) (i : S) (s : Finset ι)
    (U : ι → Act → S → ℝ≥0∞) :
    fa_initialAvg M θ i (fun a j => ∑ t ∈ s, U t a j)=∑ t ∈ s, fa_initialAvg M θ i (U t) := by
  induction s using Finset.induction_on with
  | empty => simp [fa_initialAvg]
  | insert t s ht ih => simp only [Finset.sum_insert ht,fa_initialAvg_add,ih]

lemma fa_expectedCost_first (M : MDC S Act) (θ : M.Policy) (i : S) (t : ℕ) :
    MDC.expectedCost θ i (t+1)=fa_initialAvg M θ i
      (fun a j => MDC.expectedCost (θ.shift i a) j t) := by
  simp_rw [fa_expectedCost]
  unfold fa_initialAvg
  simpa only [MDC.Policy.shift] using fa_first_step_expect M θ i t
    (fun h j => ∑ a ∈ M.A j, θ.σ h j a*(M.C j a : ℝ≥0∞))

lemma fa_expectedTerminal_first (M : MDC S Act) (F : S → ℝ≥0) (θ : M.Policy) (i : S) (t : ℕ) :
    MDC.expectedTerminal F θ i (t+1)=fa_initialAvg M θ i
      (fun a j => MDC.expectedTerminal F (θ.shift i a) j t) := by
  simp_rw [fa_expectedTerminal]
  unfold fa_initialAvg fa_expect
  exact fa_first_step_expect M θ i t (fun _ j => F j)

lemma fa_initialCost (M : MDC S Act) (θ : M.Policy) (i : S) :
    MDC.expectedCost θ i 0=∑ a ∈ M.A i, θ.σ [] i a*(M.C i a : ℝ≥0∞) := by
  rw [fa_expectedCost,fa_tsum_list]
  simp [MDC.histProb]

lemma fa_horizon_zero (M : MDC S Act) (F : S → ℝ≥0) (θ : M.Policy) (α : ℝ≥0) (i : S) :
    MDC.horizonCost F α θ 0 i=(F i : ℝ≥0∞) := by
  simp [MDC.horizonCost,fa_expectedTerminal,fa_expect_zero]

lemma fa_horizon_rec (M : MDC S Act) (F : S → ℝ≥0) (θ : M.Policy) (α : ℝ≥0) (n : ℕ) (i : S) :
    MDC.horizonCost F α θ (n+1) i=
      (∑ a ∈ M.A i, θ.σ [] i a*(M.C i a : ℝ≥0∞))+
        (α : ℝ≥0∞)*fa_initialAvg M θ i (fun a j => MDC.horizonCost F α (θ.shift i a) n j) := by
  have hsum : fa_initialAvg M θ i (fun a j => MDC.horizonCost F α (θ.shift i a) n j)=
      (∑ t ∈ Finset.range n, (α : ℝ≥0∞)^t*fa_initialAvg M θ i
        (fun a j => MDC.expectedCost (θ.shift i a) j t))+
      (α : ℝ≥0∞)^n*fa_initialAvg M θ i (fun a j => MDC.expectedTerminal F (θ.shift i a) j n) := by
    unfold MDC.horizonCost
    rw [fa_initialAvg_add,fa_initialAvg_sum,fa_initialAvg_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    exact fa_initialAvg_mul M θ i _ _
  rw [hsum]
  unfold MDC.horizonCost
  rw [Finset.sum_range_succ',fa_initialCost,fa_expectedTerminal_first]
  simp_rw [fa_expectedCost_first]
  rw [mul_add,Finset.mul_sum]
  simp only [pow_succ,pow_zero,one_mul]
  have hh : (∑ t ∈ Finset.range n, (α : ℝ≥0∞)^t*(α : ℝ≥0∞)*
      fa_initialAvg M θ i (fun a j => MDC.expectedCost (θ.shift i a) j t))=
      ∑ t ∈ Finset.range n, (α : ℝ≥0∞)*((α : ℝ≥0∞)^t*
        fa_initialAvg M θ i (fun a j => MDC.expectedCost (θ.shift i a) j t)) := by
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [hh]
  rw [← Finset.mul_sum]
  ring

end
end SennottDP.BlackwellFH



namespace SennottDP.BlackwellFH
open scoped ENNReal NNReal
open Classical Filter Topology
noncomputable section

lemma fa_tsum_iSup {ι : Type*} (F : ℕ → ι → ℝ≥0∞) (hF : ∀ j, Monotone (fun n => F n j)) :
    (∑' j, ⨆ n, F n j)=⨆ n, ∑' j, F n j := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  have he (s : Finset ι) : (∑ j ∈ s, ⨆ n, F n j)=⨆ n, ∑ j ∈ s, F n j :=
    ENNReal.finsetSum_iSup_of_monotone hF
  simp_rw [he]
  rw [iSup_comm]

lemma fa_tail_mono (u : ℕ → ℝ≥0∞) : Monotone (fun n => ⨅ k : ℕ, u (k+n)) := by
  intro n m hnm
  apply le_iInf
  intro k
  have he : (k+m-n)+n=k+m := by omega
  exact (iInf_le (fun k => u (k+n)) (k+m-n)).trans_eq (congrArg u he)

lemma fa_tsum_liminf {ι : Type*} (F : ℕ → ι → ℝ≥0∞) :
    (∑' j, liminf (fun n => F n j) atTop) ≤ liminf (fun n => ∑' j, F n j) atTop := by
  simp only [liminf_eq_iSup_iInf_of_nat']
  rw [fa_tsum_iSup _ (fun j => fa_tail_mono (fun n => F n j))]
  apply iSup_le
  intro n
  calc
    _ ≤ ⨅ k : ℕ, ∑' j, F (k+n) j := by
      apply le_iInf
      intro k
      exact ENNReal.tsum_le_tsum (fun j => iInf_le (fun k => F (k+n) j) k)
    _ ≤ _ := le_iSup (fun n => ⨅ k : ℕ, ∑' j, F (k+n) j) n

lemma fa_inf'_mono {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (F G : ι → ℝ≥0∞) (h : ∀ j ∈ s, F j ≤ G j) : s.inf' hs F ≤ s.inf' hs G := by
  apply Finset.le_inf'
  intro j hj
  exact (Finset.inf'_le _ hj).trans (h j hj)

lemma fa_inf'_iSup {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (F : ℕ → ι → ℝ≥0∞)
    (hF : ∀ j ∈ s, Monotone (fun n => F n j)) :
    s.inf' hs (fun j => ⨆ n, F n j)=⨆ n, s.inf' hs (F n) := by
  induction s using Finset.cons_induction with
  | empty => simp [Finset.Nonempty] at hs
  | cons a s ha ih =>
    by_cases he : s.Nonempty
    · have hF' : ∀ j ∈ s, Monotone (fun n => F n j) :=
        fun j hj => hF j (Finset.mem_cons_of_mem hj)
      have hm : Monotone (fun n => s.inf' he (F n)) :=
        fun r t hrt => fa_inf'_mono s he _ _ (fun j hj => hF' j hj hrt)
      rw [Finset.inf'_cons he,ih he hF']
      rw [← iSup_inf_of_monotone (hF a (Finset.mem_cons_self _ _)) hm]
      apply iSup_congr
      intro n
      rw [Finset.inf'_cons he]
    · have hse : s=∅ := Finset.not_nonempty_iff_eq_empty.mp he
      subst s
      simp

lemma fa_inf'_iInf {ι κ : Type*} (s : Finset ι) (hs : s.Nonempty) (F : κ → ι → ℝ≥0∞) :
    s.inf' hs (fun j => ⨅ k, F k j)=⨅ k, s.inf' hs (F k) := by
  apply le_antisymm
  · apply le_iInf
    intro k
    apply Finset.le_inf'
    intro j hj
    exact (Finset.inf'_le _ hj).trans (iInf_le (fun k => F k j) k)
  · apply Finset.le_inf'
    intro j hj
    apply le_iInf
    intro k
    exact (iInf_le (fun k => s.inf' hs (F k)) k).trans (Finset.inf'_le _ hj)

lemma fa_inf'_liminf {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (F : ℕ → ι → ℝ≥0∞) :
    s.inf' hs (fun j => liminf (fun n => F n j) atTop)=
      liminf (fun n => s.inf' hs (F n)) atTop := by
  simp only [liminf_eq_iSup_iInf_of_nat']
  rw [fa_inf'_iSup s hs _ (fun j _ => fa_tail_mono (fun n => F n j))]
  apply iSup_congr
  intro n
  exact fa_inf'_iInf s hs (fun k => F (k+n))

lemma fa_liminf_add (a : ℝ≥0∞) (u : ℕ → ℝ≥0∞) :
    liminf (fun n => a+u n) atTop=a+liminf u atTop := by
  simp only [liminf_eq_iSup_iInf_of_nat']
  rw [ENNReal.add_iSup]
  apply iSup_congr
  intro n
  rw [ENNReal.add_iInf]

end
end SennottDP.BlackwellFH


open scoped ENNReal NNReal

namespace SennottDP.AvgFinite.C455

open SennottDP.AvgFinite

variable {S : Type*} {Act : Type*} [Countable S]

theorem c455_list_tsum {α : Type*} (f : List α → ℝ≥0∞) (hf : f [] = 0) :
    ∑' h, f h = ∑' p : α × List α, f (p.1 :: p.2) := by
  have hinj : Function.Injective (fun p : α × List α => p.1 :: p.2) := by
    intro p q h
    simp only [List.cons.injEq] at h
    exact Prod.ext h.1 h.2
  refine (hinj.tsum_eq ?_).symm
  intro h hh
  cases h with
  | nil => exact (hh hf).elim
  | cons x l => exact ⟨(x, l), rfl⟩

theorem c455_prev_sum (M : MDC S Act) (i : S) (rest : List (S × Act)) :
    ∑' j, prevWeight M i rest j = 1 := by
  cases rest with
  | nil =>
    classical
    show ∑' j, (if j = i then (1 : ℝ≥0∞) else 0) = 1
    simp
  | cons x l =>
    obtain ⟨k, b⟩ := x
    exact M.P_sum k b

theorem c455_mass {M : MDC S Act} (θ : Policy M) (i : S) :
    ∀ t, ∑' h : List (S × Act), (if h.length = t then histProb θ i h else 0) = 1 := by
  intro t
  induction t with
  | zero =>
    rw [tsum_eq_single []]
    · simp [histProb]
    · intro h hh
      rw [if_neg]
      intro hl; exact hh (List.length_eq_zero_iff.mp hl)
  | succ t ih =>
    rw [c455_list_tsum _ (by simp)]
    refine (ENNReal.tsum_prod (f := fun (x : S × Act) (rest : List (S × Act)) =>
      if (x :: rest).length = t + 1 then histProb θ i (x :: rest) else 0)).trans ?_
    rw [ENNReal.tsum_comm, ← ih]
    refine tsum_congr fun rest => ?_
    by_cases hr : rest.length = t
    · rw [if_pos hr]
      have : ∀ x : S × Act, (if (x :: rest).length = t + 1 then histProb θ i (x :: rest) else 0) =
          histProb θ i rest * (prevWeight M i rest x.1 * θ.prob rest x.1 x.2) := by
        intro x
        rw [if_pos (by simp [hr])]
        obtain ⟨j, a⟩ := x
        simp only [histProb, mul_assoc]
      rw [tsum_congr this, ENNReal.tsum_mul_left]
      conv_rhs => rw [← mul_one (histProb θ i rest)]
      congr 1
      refine (ENNReal.tsum_prod (f := fun (j : S) (a : Act) =>
        prevWeight M i rest j * θ.prob rest j a)).trans ?_
      have h2 : ∀ j, ∑' a, prevWeight M i rest j * θ.prob rest j a = prevWeight M i rest j := by
        intro j
        rw [ENNReal.tsum_mul_left, tsum_eq_sum (s := M.A j) (fun a ha => θ.prob_supp rest j a ha),
          θ.prob_sum, mul_one]
      rw [tsum_congr h2, c455_prev_sum]
    · rw [if_neg hr]
      refine ENNReal.tsum_eq_zero.mpr fun x => ?_
      rw [if_neg (by simp [hr])]

theorem c455_expCost_le {M : MDC S Act} (B : ℝ≥0) (hB : ∀ i, ∀ a ∈ M.A i, M.C i a ≤ B)
    (θ : Policy M) (i : S) (t : ℕ) : expCost θ i t ≤ B := by
  unfold expCost
  calc ∑' h : List (S × Act), (if h.length = t + 1 then histProb θ i h * lastCost M h else 0)
      ≤ ∑' h : List (S × Act), (B : ℝ≥0∞) * (if h.length = t + 1 then histProb θ i h else 0) := by
        refine ENNReal.tsum_le_tsum fun h => ?_
        split_ifs with hl
        · cases h with
          | nil => simp at hl
          | cons x rest =>
            obtain ⟨j, a⟩ := x
            by_cases ha : a ∈ M.A j
            · rw [mul_comm (B : ℝ≥0∞)]
              exact mul_le_mul_of_nonneg_left
                (show (M.C j a : ℝ≥0∞) ≤ B by exact_mod_cast hB j a ha) bot_le
            · have : histProb θ i ((j, a) :: rest) = 0 := by
                simp [histProb, θ.prob_supp rest j a ha]
              simp [this]
        · simp
    _ = B := by rw [ENNReal.tsum_mul_left, c455_mass θ i (t + 1), mul_one]

theorem c455_mono {M : MDC S Act} (θ : Policy M) (i : S) {α β : ℝ} (h : α ≤ β) :
    discCost θ α i ≤ discCost θ β i := by
  unfold discCost
  refine ENNReal.tsum_le_tsum fun t => ?_
  gcongr

theorem c455_incr {M : MDC S Act} (B : ℝ≥0) (hB : ∀ i, ∀ a ∈ M.A i, M.C i a ≤ B)
    (θ : Policy M) (i : S) {α β : ℝ} (h0 : 0 < α) (h : α ≤ β) (h1 : β < 1) :
    discCost θ β i ≤ discCost θ α i + B * ENNReal.ofReal (1 / (1 - β) - 1 / (1 - α)) := by
  have hβ0 : 0 ≤ β := by linarith
  have hsum : ∑' t : ℕ, ENNReal.ofReal (β ^ t - α ^ t) = ENNReal.ofReal (1 / (1 - β) - 1 / (1 - α)) := by
    have sβ := summable_geometric_of_lt_one hβ0 h1
    have sα := summable_geometric_of_lt_one h0.le (by linarith)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => sub_nonneg.mpr (pow_le_pow_left₀ h0.le h t))
      (sβ.sub sα), sβ.tsum_sub sα, tsum_geometric_of_lt_one hβ0 h1,
      tsum_geometric_of_lt_one h0.le (by linarith), one_div, one_div]
  rw [← hsum, ← ENNReal.tsum_mul_left]
  unfold discCost
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun t => ?_
  have e : ENNReal.ofReal β ^ t = ENNReal.ofReal α ^ t + ENNReal.ofReal (β ^ t - α ^ t) := by
    rw [← ENNReal.ofReal_pow hβ0, ← ENNReal.ofReal_pow h0.le, ← ENNReal.ofReal_add
      (pow_nonneg h0.le t) (sub_nonneg.mpr (pow_le_pow_left₀ h0.le h t))]
    congr 1; ring
  rw [e, add_mul]
  refine add_le_add le_rfl ?_
  rw [mul_comm (B : ℝ≥0∞)]
  exact mul_le_mul_of_nonneg_left (c455_expCost_le B hB θ i t) bot_le

end SennottDP.AvgFinite.C455

open SennottDP.AvgFinite SennottDP.AvgFinite.C455 in
theorem _root_.SennottDP.AvgFinite.cor_4_5_5_bounded_continuous {S : Type*} {Act : Type*} [Countable S] (M : MDC S Act)
    (hB : ∃ B : ℝ≥0, ∀ i, ∀ a ∈ M.A i, M.C i a ≤ B) (i : S) :
    (∀ α ∈ Set.Ioo (0 : ℝ) 1, discValue M α i ≠ ⊤) ∧
    ContinuousOn (fun α : ℝ => (discValue M α i).toReal) (Set.Ioo 0 1) := by
  obtain ⟨B, hB⟩ := hB
  classical
  let θ0 : Policy M := StationaryPolicy.toPolicy
    ⟨fun j => (M.A_nonempty j).choose, fun j => (M.A_nonempty j).choose_spec⟩
  have hfin : ∀ α ∈ Set.Ioo (0 : ℝ) 1, discValue M α i ≠ ⊤ := by
    intro α hα
    have h1 : discValue M α i ≤ discCost θ0 α i := iInf_le _ θ0
    refine ne_top_of_le_ne_top ?_ h1
    have hα1 : ENNReal.ofReal α < 1 := by rw [ENNReal.ofReal_lt_one]; exact hα.2
    refine ne_top_of_le_ne_top (b := ∑' t : ℕ, ENNReal.ofReal α ^ t * B) ?_ ?_
    · rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
      exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hα1).ne') ENNReal.coe_ne_top
    · exact ENNReal.tsum_le_tsum fun t => mul_le_mul_of_nonneg_left (c455_expCost_le B hB θ0 i t) bot_le
  refine ⟨hfin, ?_⟩
  set f : ℝ → ℝ := fun α => (discValue M α i).toReal with hf
  set g : ℝ → ℝ := fun α => (B : ℝ) * (1 / (1 - α)) with hg
  -- sandwich: for α ≤ β in (0,1), f α ≤ f β ≤ f α + (g β - g α)
  have hsand : ∀ α ∈ Set.Ioo (0 : ℝ) 1, ∀ β ∈ Set.Ioo (0 : ℝ) 1, α ≤ β →
      f α ≤ f β ∧ f β ≤ f α + (g β - g α) := by
    intro α hα β hβ hab
    have hmono : discValue M α i ≤ discValue M β i :=
      iInf_mono fun θ => c455_mono θ i hab
    have hinc : discValue M β i ≤ discValue M α i + B * ENNReal.ofReal (1 / (1 - β) - 1 / (1 - α)) := by
      unfold discValue
      rw [ENNReal.iInf_add]
      exact iInf_mono fun θ => c455_incr B hB θ i hα.1 hab hβ.2
    have hg0 : 0 ≤ 1 / (1 - β) - 1 / (1 - α) := by
      have : 1 / (1 - α) ≤ 1 / (1 - β) :=
        one_div_le_one_div_of_le (by linarith [(Set.mem_Ioo.mp hβ).2]) (by linarith)
      linarith
    refine ⟨ENNReal.toReal_mono (hfin β hβ) hmono, ?_⟩
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin α hα,
      ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top⟩) hinc
    rw [ENNReal.toReal_add (hfin α hα) (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hg0, ENNReal.coe_toReal] at this
    simp only [hf, hg]
    linarith
  have hgc : ContinuousOn g (Set.Ioo 0 1) := by
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.div continuousOn_const
      (continuousOn_const.sub continuousOn_id) ?_)
    intro x hx; have := (Set.mem_Ioo.mp hx).2; linarith
  intro x hx
  have hgx := hgc x hx
  rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds] at hgx ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := hgx ε hε
  refine ⟨δ, hδ, fun y hy hyd => ?_⟩
  have hgy := hδg hy hyd
  rw [Real.dist_eq] at hgy ⊢
  rcases le_total x y with hxy | hyx
  · obtain ⟨h1, h2⟩ := hsand x hx y hy hxy
    rw [abs_lt] at hgy ⊢; constructor <;> linarith
  · obtain ⟨h1, h2⟩ := hsand y hy x hx hyx
    rw [abs_lt] at hgy ⊢; constructor <;> linarith




namespace SennottDP.AvgFinite
open scoped ENNReal NNReal
open Classical Filter Topology
noncomputable section
variable {S Act : Type*} [Countable S]

def bf_model (M : MDC S Act) : SennottDP.BlackwellFH.MDC S Act where
  A := M.A
  A_nonempty := M.A_nonempty
  C := M.C
  P := M.P
  P_sum i a _ := M.P_sum i a

def bf_policy (M : MDC S Act) (θ : Policy M) : (bf_model M).Policy where
  σ := θ.prob
  σ_sum := θ.prob_sum
  σ_supp := θ.prob_supp

def bf_policyBack (M : MDC S Act) (θ : (bf_model M).Policy) : Policy M where
  prob := θ.σ
  prob_sum := θ.σ_sum
  prob_supp := θ.σ_supp

lemma bf_policy_inverse (M : MDC S Act) (θ : (bf_model M).Policy) :
    bf_policy M (bf_policyBack M θ) = θ := by cases θ; rfl

lemma bf_hist (M : MDC S Act) (θ : Policy M) (i : S) (t : ℕ)
    (h : List (S × Act)) (j : S) :
    SennottDP.BlackwellFH.MDC.histProb (bf_policy M θ) i t h j =
      if h.length = t then histProb θ i h * prevWeight M i h j else 0 := by
  induction t generalizing h j with
  | zero => cases h <;> simp [SennottDP.BlackwellFH.MDC.histProb,histProb,prevWeight]
  | succ t ih =>
    cases h with
    | nil => simp [SennottDP.BlackwellFH.MDC.histProb]
    | cons p h =>
      rcases p with ⟨k,a⟩
      simp only [SennottDP.BlackwellFH.MDC.histProb,ih,List.length_cons,histProb,prevWeight]
      by_cases hl : h.length = t
      · simp [hl,bf_policy,bf_model,mul_assoc]
      · simp [hl]

lemma bf_expectedCost (M : MDC S Act) (θ : Policy M) (i : S) (t : ℕ) :
    SennottDP.BlackwellFH.MDC.expectedCost (bf_policy M θ) i t = expCost θ i t := by
  rw [SennottDP.BlackwellFH.fa_expectedCost]
  have hr : expCost θ i t = ∑' h : List (S × Act), ∑' j : S, ∑' a : Act,
      if ((j,a)::h).length = t+1 then histProb θ i ((j,a)::h) * lastCost M ((j,a)::h) else 0 := by
    unfold expCost
    rw [C455.c455_list_tsum _ (by simp),ENNReal.tsum_prod',ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_prod']
  rw [hr]
  apply tsum_congr
  intro h
  apply tsum_congr
  intro j
  rw [bf_hist]
  by_cases hl : h.length = t
  · simp only [hl,if_true,List.length_cons,histProb,lastCost]
    rw [Finset.mul_sum]
    rw [tsum_eq_sum (s := M.A j) (f := fun a : Act => histProb θ i h * prevWeight M i h j * θ.prob h j a * (M.C j a : ℝ≥0∞)) (fun a ha => by simp [θ.prob_supp h j a ha])]
    apply Finset.sum_congr rfl
    intro a _
    simp [bf_policy,bf_model,mul_assoc]
  · simp [hl]

lemma bf_horizon (M : MDC S Act) (θ : Policy M) (α : ℝ≥0) (n : ℕ) (i : S) :
    SennottDP.BlackwellFH.MDC.horizonCost (fun _ => 0) α (bf_policy M θ) n i =
      ∑ t ∈ Finset.range n, (α : ℝ≥0∞)^t * expCost θ i t := by
  unfold SennottDP.BlackwellFH.MDC.horizonCost
  rw [SennottDP.BlackwellFH.fa_expectedTerminal]
  simp only [SennottDP.BlackwellFH.fa_expect,ENNReal.coe_zero,mul_zero,tsum_zero,add_zero]
  apply Finset.sum_congr rfl
  intro t _
  rw [bf_expectedCost]

lemma bf_expCost_zero (M : MDC S Act) (e : StationaryPolicy M) (i : S) :
    expCost e.toPolicy i 0 = (M.C i (e.f i) : ℝ≥0∞) := by
  rw [← bf_expectedCost, SennottDP.BlackwellFH.fa_initialCost]
  simp [bf_policy,bf_model,StationaryPolicy.toPolicy,e.mem i]

lemma bf_expCost_succ (M : MDC S Act) (e : StationaryPolicy M) (i : S) (t : ℕ) :
    expCost e.toPolicy i (t+1) = ∑' j, M.P i (e.f i) j * expCost e.toPolicy j t := by
  rw [← bf_expectedCost,SennottDP.BlackwellFH.fa_expectedCost_first]
  have hs (k : S) (a : Act) : (bf_policy M e.toPolicy).shift k a = bf_policy M e.toPolicy := rfl
  simp only [SennottDP.BlackwellFH.fa_initialAvg,hs,bf_expectedCost]
  simp [bf_policy,bf_model,StationaryPolicy.toPolicy,e.mem i]

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal
open Classical Filter Topology
open SennottDP.BlackwellFH
noncomputable section
variable {S Act : Type*} [Countable S]

def bf_iter (M : MDC S Act) (α : ℝ≥0) : ℕ → S → ℝ≥0∞ :=
  fa_iter (bf_model M) (fun _ => 0) α

def bf_limit (M : MDC S Act) (α : ℝ≥0) (i : S) : ℝ≥0∞ := ⨆ n, bf_iter M α n i

lemma bf_Q_mono (M : MDC S Act) (α : ℝ≥0) (U W : S → ℝ≥0∞)
    (h : ∀ j, U j ≤ W j) (i : S) (a : Act) :
    fa_Q (bf_model M) α U i a ≤ fa_Q (bf_model M) α W i a := by
  unfold fa_Q
  exact add_le_add le_rfl (mul_le_mul_right
    (ENNReal.tsum_le_tsum (fun j => mul_le_mul_right (h j) (M.P i a j))) _)

lemma bf_T_mono (M : MDC S Act) (α : ℝ≥0) (U W : S → ℝ≥0∞)
    (h : ∀ j, U j ≤ W j) (i : S) : fa_T (bf_model M) α U i ≤ fa_T (bf_model M) α W i :=
  fa_inf'_mono _ _ _ _ (fun a _ => bf_Q_mono M α U W h i a)

lemma bf_Q_iSup (M : MDC S Act) (α : ℝ≥0) (U : ℕ → S → ℝ≥0∞)
    (hU : ∀ j, Monotone (fun n => U n j)) (i : S) (a : Act) :
    fa_Q (bf_model M) α (fun j => ⨆ n, U n j) i a = ⨆ n, fa_Q (bf_model M) α (U n) i a := by
  unfold fa_Q
  simp only [bf_model]
  simp_rw [ENNReal.mul_iSup]
  rw [fa_tsum_iSup (fun n j => M.P i a j * U n j)
    (fun j r s hrs => mul_le_mul_right (hU j hrs) (M.P i a j))]
  rw [ENNReal.mul_iSup,ENNReal.add_iSup]

lemma bf_iter_mono (M : MDC S Act) (α : ℝ≥0) (i : S) : Monotone (fun n => bf_iter M α n i) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n generalizing i with
  | zero => exact bot_le
  | succ n ih => exact bf_T_mono M α _ _ ih i

lemma bf_limit_fixed (M : MDC S Act) (α : ℝ≥0) (i : S) :
    bf_limit M α i = fa_T (bf_model M) α (bf_limit M α) i := by
  have hT : fa_T (bf_model M) α (bf_limit M α) i = ⨆ n, fa_T (bf_model M) α (bf_iter M α n) i := by
    unfold fa_T bf_limit
    simp_rw [bf_Q_iSup M α (bf_iter M α) (bf_iter_mono M α)]
    exact fa_inf'_iSup _ _ _ (fun a _ r s hrs => bf_Q_mono M α _ _ (fun j => bf_iter_mono M α j hrs) i a)
  rw [hT]
  change (⨆ n, bf_iter M α n i) = ⨆ n, bf_iter M α (n+1) i
  apply le_antisymm
  · apply iSup_le
    intro n
    exact (bf_iter_mono M α i (Nat.le_succ n)).trans (le_iSup (fun n => bf_iter M α (n+1) i) n)
  · apply iSup_le
    intro n
    exact le_iSup (fun n => bf_iter M α n i) (n+1)

lemma bf_stationary_supersolution (M : MDC S Act) (α : ℝ≥0) (f : S → Act)
    (hf : ∀ i, f i ∈ M.A i) (U : S → ℝ≥0∞)
    (hU : ∀ i, fa_Q (bf_model M) α U i (f i) ≤ U i) :
    ∀ i, discCost (StationaryPolicy.toPolicy ⟨f,hf⟩) α i ≤ U i := by
  let e : StationaryPolicy M := ⟨f,hf⟩
  let θ := bf_policy M e.toPolicy
  have hshift (i : S) (a : Act) : θ.shift i a = θ := rfl
  have hcost (n : ℕ) (i : S) : SennottDP.BlackwellFH.MDC.horizonCost (fun _ => 0) α θ n i ≤ U i := by
    induction n generalizing i with
    | zero => simp [fa_horizon_zero]
    | succ n ih =>
      have hrec : SennottDP.BlackwellFH.MDC.horizonCost (fun _ => 0) α θ (n+1) i =
          (M.C i (f i) : ℝ≥0∞) + (α : ℝ≥0∞) * ∑' j, M.P i (f i) j *
            SennottDP.BlackwellFH.MDC.horizonCost (fun _ => 0) α θ n j := by
        rw [fa_horizon_rec]
        simp only [fa_initialAvg,hshift]
        simp [θ,e,bf_policy,bf_model,StationaryPolicy.toPolicy,hf i]
      rw [hrec]
      apply le_trans ?_ (hU i)
      exact add_le_add le_rfl (mul_le_mul_right (ENNReal.tsum_le_tsum
        (fun j => mul_le_mul_right (ih j) (M.P i (f i) j))) _)
  intro i
  rw [discCost,ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro n
  have hc := hcost n i
  change SennottDP.BlackwellFH.MDC.horizonCost (fun _ => 0) α (bf_policy M e.toPolicy) n i ≤ U i at hc
  rw [bf_horizon] at hc
  simpa using hc

lemma bf_value_eq_limit (M : MDC S Act) (α : ℝ≥0) : discValue M α = bf_limit M α := by
  have hl (i : S) : bf_limit M α i ≤ discValue M α i := by
    apply iSup_le
    intro n
    apply le_iInf
    intro θ
    have h := fa_iter_le_cost (bf_model M) (fun _ => 0) (bf_policy M θ) α n i
    rw [bf_horizon] at h
    exact h.trans (by
      simpa [discCost] using (ENNReal.sum_le_tsum (Finset.range n)
        (f := fun t => (α : ℝ≥0∞)^t * expCost θ i t)))
  obtain ⟨f,hf⟩ := fa_selector (bf_model M) α (bf_limit M α)
  have hc := bf_stationary_supersolution M α f.1 f.2 (bf_limit M α)
    (fun i => (hf i).trans (bf_limit_fixed M α i).symm |>.le)
  ext i
  exact le_antisymm ((iInf_le _ (StationaryPolicy.toPolicy ⟨f.1,f.2⟩)).trans (hc i)) (hl i)

lemma bf_discount_optimal_exists (M : MDC S Act) (α : ℝ≥0) :
    ∃ e : StationaryPolicy M, IsDiscountOptimal e.toPolicy α := by
  obtain ⟨f,hf⟩ := fa_selector (bf_model M) α (bf_limit M α)
  refine ⟨⟨f.1,f.2⟩,fun i => ?_⟩
  apply le_antisymm
  · rw [bf_value_eq_limit]
    exact bf_stationary_supersolution M α f.1 f.2 (bf_limit M α)
      (fun i => (hf i).trans (bf_limit_fixed M α i).symm |>.le) i
  · exact iInf_le _ _

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal
open Classical Filter Topology
open SennottDP.BlackwellFH
noncomputable section
variable {S Act : Type*} [Countable S]

lemma bf_Q_both_mono (M : MDC S Act) {α β : ℝ≥0} (hα : α ≤ β) (U W : S → ℝ≥0∞)
    (hW : ∀ j, U j ≤ W j) (i : S) (a : Act) :
    fa_Q (bf_model M) α U i a ≤ fa_Q (bf_model M) β W i a := by
  unfold fa_Q
  gcongr
  exact hW j

lemma bf_iter_alpha_mono (M : MDC S Act) (n : ℕ) (i : S) : Monotone (fun α : ℝ≥0 => bf_iter M α n i) := by
  intro α β hα
  induction n generalizing i with
  | zero => exact le_rfl
  | succ n ih =>
    change fa_T (bf_model M) α (bf_iter M α n) i ≤ fa_T (bf_model M) β (bf_iter M β n) i
    exact fa_inf'_mono ((bf_model M).A i) ((bf_model M).A_nonempty i) _ _ (fun a _ => bf_Q_both_mono M hα _ _ ih i a)

lemma bf_mul_diagonal (f g : ℕ → ℝ≥0∞) (hf : Monotone f) (hg : Monotone g) :
    (⨆ n, f n) * (⨆ n, g n) = ⨆ n, f n * g n := by
  rw [ENNReal.iSup_mul]
  simp_rw [ENNReal.mul_iSup]
  apply le_antisymm
  · refine iSup_le (fun n => iSup_le (fun m => ?_))
    exact (mul_le_mul' (hf (Nat.le_max_left n m)) (hg (Nat.le_max_right n m))).trans (le_iSup (fun k => f k * g k) (max n m))
  · refine iSup_le (fun n => ?_)
    exact (le_iSup_of_le n (le_iSup (fun m => f n * g m) n))

lemma bf_iter_param_iSup (M : MDC S Act) (a : ℕ → ℝ≥0) (ha : Monotone a) (β : ℝ≥0)
    (hs : (⨆ n, (a n : ℝ≥0∞)) = (β : ℝ≥0∞)) (N : ℕ) (i : S) :
    bf_iter M β N i = ⨆ n, bf_iter M (a n) N i := by
  induction N generalizing i with
  | zero => simp [bf_iter,fa_iter]
  | succ N ih =>
    have hQ (i : S) (b : Act) :
        fa_Q (bf_model M) β (bf_iter M β N) i b = ⨆ n, fa_Q (bf_model M) (a n) (bf_iter M (a n) N) i b := by
      unfold fa_Q
      simp only [bf_model]
      simp_rw [ih,ENNReal.mul_iSup]
      rw [fa_tsum_iSup (fun n j => M.P i b j * bf_iter M (a n) N j)
        (fun j r s hrs => mul_le_mul_right (bf_iter_alpha_mono M N j (ha hrs)) (M.P i b j))]
      rw [← hs,bf_mul_diagonal (fun n => (a n : ℝ≥0∞))
        (fun n => ∑' j, M.P i b j * bf_iter M (a n) N j)
        (fun r s hrs => ENNReal.coe_le_coe.mpr (ha hrs))
        (fun r s hrs => ENNReal.tsum_le_tsum (fun j => mul_le_mul_right (bf_iter_alpha_mono M N j (ha hrs)) (M.P i b j))),ENNReal.add_iSup]
    change fa_T (bf_model M) β (bf_iter M β N) i = ⨆ n, fa_T (bf_model M) (a n) (bf_iter M (a n) N) i
    unfold fa_T
    simp_rw [hQ]
    exact fa_inf'_iSup _ _ _ (fun b _ r s hrs => bf_Q_both_mono M (ha hrs) _ _ (fun j => bf_iter_alpha_mono M N j (ha hrs)) i b)

lemma bf_value_mono (M : MDC S Act) (i : S) : Monotone (fun α : ℝ => discValue M α i) := by
  intro α β hα
  apply iInf_mono
  intro θ
  exact C455.c455_mono θ i hα

lemma bf_value_left_cont (M : MDC S Act) (i : S) {β : ℝ} (hβ : 0 < β) :
    ContinuousWithinAt (fun α : ℝ => discValue M α i) (Set.Iio β) β := by
  let βn : ℝ≥0 := ⟨β,hβ.le⟩
  obtain ⟨a,ha,hamem,hat⟩ := exists_seq_strictMono_tendsto' (show (0 : ℝ≥0) < βn from hβ)
  have hsa : (⨆ n, (a n : ℝ≥0∞)) = (βn : ℝ≥0∞) := by
    exact iSup_eq_of_tendsto (fun r s hrs => ENNReal.coe_le_coe.mpr (ha.monotone hrs))
      (ENNReal.continuous_coe.continuousAt.tendsto.comp hat)
  have he : discValue M β i = ⨆ n, discValue M (a n) i := by
    change discValue M βn i = _
    simp_rw [bf_value_eq_limit,bf_limit]
    rw [iSup_comm]
    apply iSup_congr
    intro N
    exact bf_iter_param_iSup M a ha.monotone βn hsa N i
  have hs : sSup ((fun α : ℝ => discValue M α i) '' Set.Iio β) = discValue M β i := by
    apply le_antisymm
    · apply sSup_le
      rintro v ⟨α,hα,rfl⟩
      exact bf_value_mono M i hα.le
    · rw [he]
      apply iSup_le
      intro n
      exact le_sSup ⟨(a n : ℝ), (hamem n).2, rfl⟩
  have ht := (bf_value_mono M i).tendsto_nhdsLT β
  rwa [hs] at ht

lemma bf_monotone_result (M : MDC S Act) (i : S) :
    MonotoneOn (fun α : ℝ => discValue M α i) (Set.Ioo 0 1) ∧
    ∀ β ∈ Set.Ioo (0 : ℝ) 1, ContinuousWithinAt (fun α : ℝ => discValue M α i) (Set.Iio β) β :=
  ⟨(bf_value_mono M i).monotoneOn _,fun β hβ => bf_value_left_cont M i hβ.1⟩

end
end SennottDP.AvgFinite

open SennottDP.AvgFinite

open scoped ENNReal NNReal

/-- Proposition 4.5.4 (Sennott, p. 72). For an MDC with countable state space, the discounted value
function `V_α(i)` (valued in `[0,∞]`) is increasing (nondecreasing) and left continuous in
`α ∈ (0,1)`, for every state `i`. -/
theorem solution {S : Type*} {Act : Type*} [Countable S]
    (M : MDC S Act) (i : S) :
    MonotoneOn (fun α : ℝ => discValue M α i) (Set.Ioo 0 1) ∧
    ∀ β ∈ Set.Ioo (0 : ℝ) 1,
      ContinuousWithinAt (fun α : ℝ => discValue M α i) (Set.Iio β) β := by
  exact bf_monotone_result M i

#print axioms solution

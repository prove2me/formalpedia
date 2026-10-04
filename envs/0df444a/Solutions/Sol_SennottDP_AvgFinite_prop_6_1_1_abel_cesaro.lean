-- Prove2me | solution 1 for SennottDP.AvgFinite.prop_6_1_1_abel_cesaro
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T01:30:33.09899+00:00
-- url     : https://prove2.me/submissions/cf01a7cd-b599-4cb2-aa76-c55f41b6d0da

import Definitions.Def_SennottDP_AvgFinite_Criteria
import Definitions.Def_SennottDP_Tauberian_KaramataR
import Definitions.Def_SennottDP_Tauberian_PowerSeries
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


open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian

/-- Cauchy product: `(∑ α^n) U(α) = ∑ α^n w_{n+1}` (no finiteness needed in `[0,∞]`). -/
theorem bwReuse_abelian_inequalities_abelian_inequalities_key (u : ℕ → ℝ≥0∞) (α : ℝ≥0) :
    (∑' n : ℕ, (α : ℝ≥0∞) ^ n) * U u α = ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w u (n + 1) := by
  have hterm : ∀ n : ℕ, (α : ℝ≥0∞) ^ n * w u (n + 1)
      = ∑' k : ℕ, (if k ≤ n then (α : ℝ≥0∞) ^ n * u k else 0) := by
    intro n
    unfold w
    rw [Finset.mul_sum, tsum_eq_sum (s := Finset.range (n + 1))]
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
    · intro k hk
      rw [if_neg]
      intro hkn
      exact hk (Finset.mem_range.mpr (Nat.lt_succ_of_le hkn))
  have hinner : ∀ k : ℕ, ∑' n : ℕ, (if k ≤ n then (α : ℝ≥0∞) ^ n * u k else 0)
      = (∑' m : ℕ, (α : ℝ≥0∞) ^ m) * ((α : ℝ≥0∞) ^ k * u k) := by
    intro k
    have hsupp : Function.support (fun n : ℕ => if k ≤ n then (α : ℝ≥0∞) ^ n * u k else 0)
        ⊆ Set.range (fun m : ℕ => m + k) := by
      intro n hn
      by_cases hkn : k ≤ n
      · exact ⟨n - k, Nat.sub_add_cancel hkn⟩
      · rw [Function.mem_support] at hn
        exact (hn (by simp [hkn])).elim
    rw [← ENNReal.tsum_mul_right, ← (add_left_injective k).tsum_eq hsupp]
    refine tsum_congr fun m => ?_
    rw [if_pos (Nat.le_add_left k m), pow_add]
    ring
  unfold U
  simp_rw [hterm]
  rw [ENNReal.tsum_comm]
  simp_rw [hinner]
  rw [ENNReal.tsum_mul_left]

/-- `abelMean u α = (1-α) * ((1-α) * ∑ α^n w_{n+1})` for `α < 1`. -/
theorem bwReuse_abelian_inequalities_abelian_inequalities_abel_eq (u : ℕ → ℝ≥0∞) (α : ℝ≥0) (hα : α < 1) :
    abelMean u α = (1 - (α : ℝ≥0∞)) *
      ((1 - (α : ℝ≥0∞)) * ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w u (n + 1)) := by
  have hα' : (α : ℝ≥0∞) < 1 := by exact_mod_cast hα
  have h0 : (1 - (α : ℝ≥0∞)) ≠ 0 := (tsub_pos_of_lt hα').ne'
  have ht : (1 - (α : ℝ≥0∞)) ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  rw [← bwReuse_abelian_inequalities_abelian_inequalities_key, ENNReal.tsum_geometric,
    ← mul_assoc (1 - (α : ℝ≥0∞)) (1 - (α : ℝ≥0∞))⁻¹, ENNReal.mul_inv_cancel h0 ht, one_mul]
  rfl

theorem bwReuse_abelian_inequalities_abelian_inequalities_w_one (k : ℕ) : w (fun _ => (1 : ℝ≥0∞)) k = (k : ℝ≥0∞) := by
  simp [w]

theorem bwReuse_abelian_inequalities_abelian_inequalities_abel_one (α : ℝ≥0) (hα : α < 1) :
    abelMean (fun _ => (1 : ℝ≥0∞)) α = 1 := by
  have hα' : (α : ℝ≥0∞) < 1 := by exact_mod_cast hα
  have h0 : (1 - (α : ℝ≥0∞)) ≠ 0 := (tsub_pos_of_lt hα').ne'
  have ht : (1 - (α : ℝ≥0∞)) ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  simp only [abelMean, U, mul_one]
  rw [ENNReal.tsum_geometric, ENNReal.mul_inv_cancel h0 ht]

/-- `(1 - α) * K → 0` as `α → 1⁻`, for finite `K`. -/
theorem bwReuse_abelian_inequalities_abelian_inequalities_tendsto (K : ℝ≥0∞) (hK : K ≠ ⊤) :
    Tendsto (fun α : ℝ≥0 => (1 - (α : ℝ≥0∞)) * K) (𝓝[<] (1 : ℝ≥0)) (𝓝 0) := by
  lift K to ℝ≥0 using hK
  have h : Tendsto (fun α : ℝ≥0 => (1 - α) * K) (𝓝 (1 : ℝ≥0)) (𝓝 ((1 - 1) * K)) :=
    ((continuous_const.sub continuous_id).mul continuous_const).tendsto 1
  rw [tsub_self, zero_mul] at h
  have h2 := (ENNReal.tendsto_coe.mpr h).mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
  refine h2.congr fun α => ?_
  simp [ENNReal.coe_sub]

theorem bwReuse_abelian_inequalities_abelian_inequalities_upper (u : ℕ → ℝ≥0∞) :
    limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) ≤ limsup (cesaroMean u) atTop := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hL => ?_
  set L := limsup (cesaroMean u) atTop
  have hε2 : (0 : ℝ≥0∞) < ((ε / 2 : ℝ≥0) : ℝ≥0∞) := by
    have : (0 : ℝ≥0) < ε / 2 := half_pos hε
    exact_mod_cast this
  have hM : L < L + ((ε / 2 : ℝ≥0) : ℝ≥0∞) := ENNReal.lt_add_right hL.ne hε2.ne'
  set M := L + ((ε / 2 : ℝ≥0) : ℝ≥0∞)
  have hMtop : M ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hL.ne, ENNReal.coe_ne_top⟩
  have hev := eventually_lt_of_limsup_lt hM
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hev
  set N := N0 + 1
  have hwn : ∀ n, N ≤ n → w u n ≤ M * n := by
    intro n hn
    have h1 := hN0 n (by omega)
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    exact (ENNReal.div_lt_iff (Or.inl hn0) (Or.inl (ENNReal.natCast_ne_top n))).mp h1 |>.le
  set C := w u N
  have hC : C ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top hMtop (ENNReal.natCast_ne_top N))
    (hwn N le_rfl)
  have hbound : ∀ n : ℕ, w u (n + 1) ≤ C + M * w (fun _ => (1 : ℝ≥0∞)) (n + 1) := by
    intro n
    rw [bwReuse_abelian_inequalities_abelian_inequalities_w_one]
    by_cases h : n + 1 ≤ N
    · refine le_trans ?_ le_self_add
      exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)
    · refine le_trans ?_ le_add_self
      exact hwn (n + 1) (by omega)
  have hev2 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), (1 - (α : ℝ≥0∞)) * C < ((ε / 2 : ℝ≥0) : ℝ≥0∞) :=
    (bwReuse_abelian_inequalities_abelian_inequalities_tendsto C hC).eventually (gt_mem_nhds hε2)
  have hev3 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), α < 1 := self_mem_nhdsWithin
  have hfin : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), abelMean u α ≤ L + ε := by
    filter_upwards [hev2, hev3] with α h2 h3
    have hα' : (α : ℝ≥0∞) < 1 := by exact_mod_cast h3
    have h0 : (1 - (α : ℝ≥0∞)) ≠ 0 := (tsub_pos_of_lt hα').ne'
    have ht : (1 - (α : ℝ≥0∞)) ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
    have hS : ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w u (n + 1) ≤
        C * ∑' n : ℕ, (α : ℝ≥0∞) ^ n +
          M * ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w (fun _ => (1 : ℝ≥0∞)) (n + 1) := by
      rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
      refine ENNReal.tsum_le_tsum fun n => ?_
      calc (α : ℝ≥0∞) ^ n * w u (n + 1)
          ≤ (α : ℝ≥0∞) ^ n * (C + M * w (fun _ => (1 : ℝ≥0∞)) (n + 1)) := by
            gcongr; exact hbound n
        _ = _ := by ring
    have hone := bwReuse_abelian_inequalities_abelian_inequalities_abel_one α h3
    rw [bwReuse_abelian_inequalities_abelian_inequalities_abel_eq _ α h3] at hone
    have hgeo : (1 - (α : ℝ≥0∞)) * ∑' n : ℕ, (α : ℝ≥0∞) ^ n = 1 := by
      rw [ENNReal.tsum_geometric, ENNReal.mul_inv_cancel h0 ht]
    rw [bwReuse_abelian_inequalities_abelian_inequalities_abel_eq _ α h3]
    calc (1 - (α : ℝ≥0∞)) * ((1 - (α : ℝ≥0∞)) * ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w u (n + 1))
        ≤ (1 - (α : ℝ≥0∞)) * ((1 - (α : ℝ≥0∞)) * (C * ∑' n : ℕ, (α : ℝ≥0∞) ^ n +
          M * ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w (fun _ => (1 : ℝ≥0∞)) (n + 1))) := by
          gcongr
      _ = (1 - (α : ℝ≥0∞)) * C * ((1 - (α : ℝ≥0∞)) * ∑' n : ℕ, (α : ℝ≥0∞) ^ n) +
          M * ((1 - (α : ℝ≥0∞)) * ((1 - (α : ℝ≥0∞)) *
            ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w (fun _ => (1 : ℝ≥0∞)) (n + 1))) := by ring
      _ = (1 - (α : ℝ≥0∞)) * C + M := by rw [hgeo, hone, mul_one, mul_one]
      _ ≤ ((ε / 2 : ℝ≥0) : ℝ≥0∞) + M := by gcongr
      _ = L + ε := by
          rw [add_comm, add_assoc, ← ENNReal.coe_add, add_halves]
  exact limsup_le_of_le (by isBoundedDefault) hfin

theorem bwReuse_abelian_inequalities_abelian_inequalities_lower (u : ℕ → ℝ≥0∞) :
    liminf (cesaroMean u) atTop ≤ liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) := by
  refine le_of_forall_lt_imp_le_of_dense fun m hm => ?_
  have hmtop : m ≠ ⊤ := ne_top_of_lt hm
  have hev := eventually_lt_of_lt_liminf hm
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hev
  set N := N0 + 1
  have hwn : ∀ n, N ≤ n → m * n ≤ w u n := by
    intro n hn
    have h1 := hN0 n (by omega)
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    exact ((ENNReal.lt_div_iff_mul_lt (Or.inl hn0) (Or.inl (ENNReal.natCast_ne_top n))).mp h1).le
  have hbound : ∀ n : ℕ, m * w (fun _ => (1 : ℝ≥0∞)) (n + 1) ≤ w u (n + 1) + m * N := by
    intro n
    rw [bwReuse_abelian_inequalities_abelian_inequalities_w_one]
    by_cases h : n + 1 ≤ N
    · refine le_trans ?_ le_add_self
      gcongr
    · refine le_trans ?_ le_self_add
      exact hwn (n + 1) (by omega)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ≥0∞) < ε := by exact_mod_cast hε
  have hK : m * N ≠ ⊤ := ENNReal.mul_ne_top hmtop (ENNReal.natCast_ne_top N)
  have hev2 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), (1 - (α : ℝ≥0∞)) * (m * N) < ε :=
    (bwReuse_abelian_inequalities_abelian_inequalities_tendsto _ hK).eventually (gt_mem_nhds hε')
  have hev3 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), α < 1 := self_mem_nhdsWithin
  have hfin : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), m - ε ≤ abelMean u α := by
    filter_upwards [hev2, hev3] with α h2 h3
    have hα' : (α : ℝ≥0∞) < 1 := by exact_mod_cast h3
    have h0 : (1 - (α : ℝ≥0∞)) ≠ 0 := (tsub_pos_of_lt hα').ne'
    have ht : (1 - (α : ℝ≥0∞)) ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
    have hS : m * ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w (fun _ => (1 : ℝ≥0∞)) (n + 1) ≤
        ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w u (n + 1) + (m * N) * ∑' n : ℕ, (α : ℝ≥0∞) ^ n := by
      rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
      refine ENNReal.tsum_le_tsum fun n => ?_
      calc m * ((α : ℝ≥0∞) ^ n * w (fun _ => (1 : ℝ≥0∞)) (n + 1))
          = (α : ℝ≥0∞) ^ n * (m * w (fun _ => (1 : ℝ≥0∞)) (n + 1)) := by ring
        _ ≤ (α : ℝ≥0∞) ^ n * (w u (n + 1) + m * N) := by gcongr; exact hbound n
        _ = _ := by ring
    have hone := bwReuse_abelian_inequalities_abelian_inequalities_abel_one α h3
    rw [bwReuse_abelian_inequalities_abelian_inequalities_abel_eq _ α h3] at hone
    have hgeo : (1 - (α : ℝ≥0∞)) * ∑' n : ℕ, (α : ℝ≥0∞) ^ n = 1 := by
      rw [ENNReal.tsum_geometric, ENNReal.mul_inv_cancel h0 ht]
    rw [bwReuse_abelian_inequalities_abelian_inequalities_abel_eq _ α h3, tsub_le_iff_right]
    calc m = m * ((1 - (α : ℝ≥0∞)) * ((1 - (α : ℝ≥0∞)) *
            ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w (fun _ => (1 : ℝ≥0∞)) (n + 1))) := by
          rw [hone, mul_one]
      _ = (1 - (α : ℝ≥0∞)) * ((1 - (α : ℝ≥0∞)) * (m *
            ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w (fun _ => (1 : ℝ≥0∞)) (n + 1))) := by ring
      _ ≤ (1 - (α : ℝ≥0∞)) * ((1 - (α : ℝ≥0∞)) * (∑' n : ℕ, (α : ℝ≥0∞) ^ n * w u (n + 1) +
            (m * N) * ∑' n : ℕ, (α : ℝ≥0∞) ^ n)) := by gcongr
      _ = (1 - (α : ℝ≥0∞)) * ((1 - (α : ℝ≥0∞)) * ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w u (n + 1)) +
            (1 - (α : ℝ≥0∞)) * (m * N) * ((1 - (α : ℝ≥0∞)) * ∑' n : ℕ, (α : ℝ≥0∞) ^ n) := by
          ring
      _ ≤ _ := by rw [hgeo, mul_one]; gcongr
  have := le_liminf_of_le (by isBoundedDefault) hfin
  exact tsub_le_iff_right.mp this

end SennottDP.Tauberian

open SennottDP.Tauberian in
theorem _root_.SennottDP.Tauberian.abelian_inequalities (u : ℕ → ℝ≥0∞) (_hu0 : u 0 ≠ ⊤) :
    liminf (cesaroMean u) atTop ≤ liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) ∧
      liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) ≤ limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) ∧
      limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) ≤ limsup (cesaroMean u) atTop := by
  have : (𝓝[<] (1 : ℝ≥0)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, zero_lt_one⟩
  exact ⟨bwReuse_abelian_inequalities_abelian_inequalities_lower u, liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault),
    bwReuse_abelian_inequalities_abelian_inequalities_upper u⟩




open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian.MonoAux

lemma bwReuse_abel_limit_monomial_one_sub_pow_eq (α : ℝ≥0) (hα : α ≤ 1) (k : ℕ) :
    (1 : ℝ≥0) - α ^ (k + 1) = (1 - α) * ∑ i ∈ Finset.range (k + 1), α ^ i := by
  apply NNReal.eq
  have h1 : α ^ (k + 1) ≤ 1 := pow_le_one₀ zero_le hα
  rw [NNReal.coe_sub h1, NNReal.coe_mul, NNReal.coe_sub hα, NNReal.coe_sum]
  push_cast
  rw [mul_neg_geom_sum]

end SennottDP.Tauberian.MonoAux

open scoped ENNReal NNReal Topology in open Filter SennottDP.Tauberian in
theorem _root_.SennottDP.Tauberian.abel_limit_monomial (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) (k : ℕ) :
    Tendsto (fun α : ℝ≥0 =>
        (1 - (α : ℝ≥0∞)) * ∑' n : ℕ, (α : ℝ≥0∞) ^ n * u n * ((α : ℝ≥0∞) ^ n) ^ k)
      (𝓝[<] (1 : ℝ≥0)) (𝓝 (L / ((k : ℝ≥0∞) + 1))) := by
  set g : ℝ≥0 → ℝ≥0 := fun α => ∑ i ∈ Finset.range (k + 1), α ^ i with hg
  have hgc : Continuous g := by
    rw [hg]; fun_prop
  have hg1 : g 1 = (k : ℝ≥0) + 1 := by simp [hg]
  have hgpos : ∀ α, 1 ≤ g α := by
    intro α
    simp only [hg]
    rw [Finset.sum_range_succ']
    simp
  -- limit of the inverse factor
  have hA : Tendsto (fun α : ℝ≥0 => ((g α : ℝ≥0∞))⁻¹) (𝓝[<] (1 : ℝ≥0))
      (𝓝 (((k : ℝ≥0∞) + 1))⁻¹) := by
    have h0 : Tendsto (fun α : ℝ≥0 => ((g α : ℝ≥0∞))⁻¹) (𝓝 (1 : ℝ≥0))
        (𝓝 (((g 1 : ℝ≥0) : ℝ≥0∞))⁻¹) :=
      tendsto_inv_iff.2 ((ENNReal.continuous_coe.tendsto _).comp (hgc.tendsto 1))
    rw [hg1] at h0
    push_cast at h0
    exact h0.mono_left nhdsWithin_le_nhds
  -- limit of the Abel mean at α^(k+1)
  have hpow : Tendsto (fun α : ℝ≥0 => α ^ (k + 1)) (𝓝[<] (1 : ℝ≥0)) (𝓝[<] (1 : ℝ≥0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun α : ℝ≥0 => α ^ (k + 1)) (𝓝 (1 : ℝ≥0)) (𝓝 ((1 : ℝ≥0) ^ (k + 1))) :=
        ((continuous_pow (k + 1)).tendsto 1)
      rw [one_pow] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with α hα
      exact pow_lt_one₀ zero_le (Set.mem_Iio.mp hα) (Nat.succ_ne_zero k)
  have hB := hlim.comp hpow
  have hmul := ENNReal.Tendsto.mul hA
    (Or.inl (ENNReal.inv_ne_zero.mpr (by simp))) hB
    (Or.inr (ENNReal.inv_ne_top.mpr (by simp)))
  have hlimeq : ((k : ℝ≥0∞) + 1)⁻¹ * L = L / ((k : ℝ≥0∞) + 1) := by
    rw [div_eq_mul_inv, mul_comm]
  rw [hlimeq] at hmul
  apply hmul.congr'
  filter_upwards [self_mem_nhdsWithin] with α hα
  have hα1 : α ≤ 1 := le_of_lt hα
  simp only [Function.comp_apply, abelMean, U]
  have hsum : (∑' n : ℕ, (α : ℝ≥0∞) ^ n * u n * ((α : ℝ≥0∞) ^ n) ^ k)
      = ∑' n : ℕ, ((α ^ (k + 1) : ℝ≥0) : ℝ≥0∞) ^ n * u n := by
    congr 1; funext n
    rw [ENNReal.coe_pow]; ring
  rw [hsum]
  have hfac : (1 : ℝ≥0∞) - ((α ^ (k + 1) : ℝ≥0) : ℝ≥0∞) = (1 - (α : ℝ≥0∞)) * (g α : ℝ≥0∞) := by
    rw [← ENNReal.coe_one, ← ENNReal.coe_sub, SennottDP.Tauberian.MonoAux.bwReuse_abel_limit_monomial_one_sub_pow_eq α hα1 k,
      ENNReal.coe_mul, ENNReal.coe_sub]
  rw [hfac]
  have hne0 : (g α : ℝ≥0∞) ≠ 0 := by
    have := hgpos α
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le one_pos this))
  have hnetop : (g α : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  calc ((g α : ℝ≥0∞))⁻¹ * ((1 - (α : ℝ≥0∞)) * (g α : ℝ≥0∞) * ∑' n : ℕ, ((α ^ (k + 1) : ℝ≥0) : ℝ≥0∞) ^ n * u n)
      = (((g α : ℝ≥0∞))⁻¹ * (g α : ℝ≥0∞)) * ((1 - (α : ℝ≥0∞)) * ∑' n : ℕ, ((α ^ (k + 1) : ℝ≥0) : ℝ≥0∞) ^ n * u n) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hne0 hnetop, one_mul]


open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian

/-- The real Abel-type mean `(1-α) ∑ α^n u_n g(α^n)`. -/
noncomputable def bwReuse_abel_limit_continuous_alcAr (u : ℕ → ℝ≥0∞) (g : ℝ → ℝ) (α : ℝ≥0) : ℝ :=
  (1 - (α : ℝ)) * ∑' n : ℕ, (α : ℝ) ^ n * (u n).toReal * g ((α : ℝ) ^ n)

/-- "Good" parameters: `0 < α < 1` and `U(α) < ∞`. -/
def bwReuse_abel_limit_continuous_alcGood (u : ℕ → ℝ≥0∞) (α : ℝ≥0) : Prop :=
  0 < α ∧ α < 1 ∧ U u α ≠ ⊤

theorem bwReuse_abel_limit_continuous_alcGood_fin {u : ℕ → ℝ≥0∞} {α : ℝ≥0} (h : bwReuse_abel_limit_continuous_alcGood u α) (n : ℕ) : u n ≠ ⊤ := by
  obtain ⟨h0, -, hU⟩ := h
  have hle : (α : ℝ≥0∞) ^ n * u n ≤ U u α := ENNReal.le_tsum (f := fun n => (α : ℝ≥0∞) ^ n * u n) n
  have hne : (α : ℝ≥0∞) ^ n * u n ≠ ⊤ := ne_top_of_le_ne_top hU hle
  intro hu
  apply hne
  rw [hu]
  exact ENNReal.mul_top (pow_ne_zero _ (by exact_mod_cast h0.ne'))

theorem bwReuse_abel_limit_continuous_alcGood_summable {u : ℕ → ℝ≥0∞} {α : ℝ≥0} (h : bwReuse_abel_limit_continuous_alcGood u α) :
    Summable (fun n : ℕ => (α : ℝ) ^ n * (u n).toReal) := by
  have := ENNReal.summable_toReal h.2.2
  refine this.congr fun n => ?_
  simp [ENNReal.toReal_mul, ENNReal.toReal_pow]

theorem bwReuse_abel_limit_continuous_alcGood_tsum {u : ℕ → ℝ≥0∞} {α : ℝ≥0} (h : bwReuse_abel_limit_continuous_alcGood u α) (k : ℕ) :
    (∑' n : ℕ, (α : ℝ≥0∞) ^ n * u n * ((α : ℝ≥0∞) ^ n) ^ k).toReal =
      ∑' n : ℕ, (α : ℝ) ^ n * (u n).toReal * ((α : ℝ) ^ n) ^ k := by
  rw [ENNReal.tsum_toReal_eq]
  · refine tsum_congr fun n => ?_
    simp [ENNReal.toReal_mul, ENNReal.toReal_pow]
  · intro n
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      (bwReuse_abel_limit_continuous_alcGood_fin h n)) (ENNReal.pow_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top))

theorem bwReuse_abel_limit_continuous_alcGood_one_sub {α : ℝ≥0} (h : α < 1) : (1 - (α : ℝ≥0∞)).toReal = 1 - (α : ℝ) := by
  rw [ENNReal.toReal_sub_of_le (by exact_mod_cast h.le) ENNReal.one_ne_top]
  simp

theorem bwReuse_abel_limit_continuous_alcGood_mem {α : ℝ≥0} (h : α < 1) (n : ℕ) : (α : ℝ) ^ n ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨by positivity, pow_le_one₀ (by positivity) (by exact_mod_cast h.le)⟩

theorem bwReuse_abel_limit_continuous_alc_summable_of_bound {u : ℕ → ℝ≥0∞} {α : ℝ≥0} (h : bwReuse_abel_limit_continuous_alcGood u α) (g : ℝ → ℝ) (B : ℝ)
    (hB : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x| ≤ B) :
    Summable (fun n : ℕ => (α : ℝ) ^ n * (u n).toReal * g ((α : ℝ) ^ n)) := by
  refine Summable.of_norm_bounded ((bwReuse_abel_limit_continuous_alcGood_summable h).mul_right B) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (hB _ (bwReuse_abel_limit_continuous_alcGood_mem h.2.1 n)) (by positivity)

theorem bwReuse_abel_limit_continuous_alc_bound_of_contOn (g : ℝ → ℝ) (hg : ContinuousOn g (Set.Icc 0 1)) :
    ∃ B : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  exact ⟨B, fun x hx => by simpa [Real.norm_eq_abs] using hB x hx⟩

theorem bwReuse_abel_limit_continuous_alc_eventually_good (u : ℕ → ℝ≥0∞) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) :
    ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), bwReuse_abel_limit_continuous_alcGood u α := by
  have h1 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), α < 1 := self_mem_nhdsWithin
  have h2 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), 0 < α :=
    nhdsWithin_le_nhds (lt_mem_nhds (zero_lt_one : (0 : ℝ≥0) < 1))
  have h3 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), abelMean u α < L + 1 :=
    hlim.eventually (gt_mem_nhds (ENNReal.lt_add_right hL one_ne_zero))
  filter_upwards [h1, h2, h3] with α a1 a2 a3
  refine ⟨a2, a1, ?_⟩
  have hα' : (α : ℝ≥0∞) < 1 := by exact_mod_cast a1
  have h0 : (1 - (α : ℝ≥0∞)) ≠ 0 := (tsub_pos_of_lt hα').ne'
  have hfin : abelMean u α ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le a3 le_top) |>.symm.symm
  · intro hU
    apply (lt_of_lt_of_le a3 le_top).ne
    unfold abelMean
    rw [hU, ENNReal.mul_top h0]

theorem bwReuse_abel_limit_continuous_alc_monomial (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) (k : ℕ) :
    Tendsto (bwReuse_abel_limit_continuous_alcAr u (fun x => x ^ k)) (𝓝[<] (1 : ℝ≥0))
      (𝓝 (L.toReal * ∫ x in (0 : ℝ)..1, x ^ k)) := by
  have hm := abel_limit_monomial u hu0 L hL hlim k
  have hne : L / ((k : ℝ≥0∞) + 1) ≠ ⊤ := ENNReal.div_ne_top hL (by positivity)
  have ht := (ENNReal.tendsto_toReal hne).comp hm
  have hval : (L / ((k : ℝ≥0∞) + 1)).toReal = L.toReal * ∫ x in (0 : ℝ)..1, x ^ k := by
    rw [integral_pow, ENNReal.toReal_div, ENNReal.toReal_add (by simp) (by simp)]
    simp [div_eq_mul_inv]
  rw [hval] at ht
  refine ht.congr' ?_
  filter_upwards [bwReuse_abel_limit_continuous_alc_eventually_good u L hL hlim] with α hα
  simp only [Function.comp, bwReuse_abel_limit_continuous_alcAr]
  rw [ENNReal.toReal_mul, bwReuse_abel_limit_continuous_alcGood_one_sub hα.2.1, bwReuse_abel_limit_continuous_alcGood_tsum hα]

theorem bwReuse_abel_limit_continuous_alc_one (u : ℕ → ℝ≥0∞) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) :
    Tendsto (bwReuse_abel_limit_continuous_alcAr u (fun _ => 1)) (𝓝[<] (1 : ℝ≥0)) (𝓝 L.toReal) := by
  have ht := (ENNReal.tendsto_toReal hL).comp hlim
  refine ht.congr' ?_
  filter_upwards [bwReuse_abel_limit_continuous_alc_eventually_good u L hL hlim] with α hα
  simp only [Function.comp, bwReuse_abel_limit_continuous_alcAr, abelMean, U]
  rw [ENNReal.toReal_mul, bwReuse_abel_limit_continuous_alcGood_one_sub hα.2.1]
  have := bwReuse_abel_limit_continuous_alcGood_tsum hα 0
  simp only [pow_zero, mul_one] at this
  rw [this]
  simp

theorem bwReuse_abel_limit_continuous_alc_add (u : ℕ → ℝ≥0∞) {α : ℝ≥0} (h : bwReuse_abel_limit_continuous_alcGood u α) (g₁ g₂ : ℝ → ℝ)
    (h₁ : ContinuousOn g₁ (Set.Icc 0 1)) (h₂ : ContinuousOn g₂ (Set.Icc 0 1)) :
    bwReuse_abel_limit_continuous_alcAr u (fun x => g₁ x + g₂ x) α = bwReuse_abel_limit_continuous_alcAr u g₁ α + bwReuse_abel_limit_continuous_alcAr u g₂ α := by
  obtain ⟨B₁, hB₁⟩ := bwReuse_abel_limit_continuous_alc_bound_of_contOn g₁ h₁
  obtain ⟨B₂, hB₂⟩ := bwReuse_abel_limit_continuous_alc_bound_of_contOn g₂ h₂
  unfold bwReuse_abel_limit_continuous_alcAr
  rw [← mul_add, ← (bwReuse_abel_limit_continuous_alc_summable_of_bound h g₁ B₁ hB₁).tsum_add
    (bwReuse_abel_limit_continuous_alc_summable_of_bound h g₂ B₂ hB₂)]
  congr 1
  exact tsum_congr fun n => by ring

theorem bwReuse_abel_limit_continuous_alc_smul (u : ℕ → ℝ≥0∞) (α : ℝ≥0) (g : ℝ → ℝ) (c : ℝ) :
    bwReuse_abel_limit_continuous_alcAr u (fun x => c * g x) α = c * bwReuse_abel_limit_continuous_alcAr u g α := by
  unfold bwReuse_abel_limit_continuous_alcAr
  beta_reduce
  rw [show (∑' n : ℕ, (α : ℝ) ^ n * (u n).toReal * (c * g ((α : ℝ) ^ n))) =
      ∑' n : ℕ, c * ((α : ℝ) ^ n * (u n).toReal * g ((α : ℝ) ^ n)) from
      tsum_congr fun n => by ring, tsum_mul_left]
  ring

theorem bwReuse_abel_limit_continuous_alc_poly (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) (p : Polynomial ℝ) :
    Tendsto (bwReuse_abel_limit_continuous_alcAr u (fun x => p.eval x)) (𝓝[<] (1 : ℝ≥0))
      (𝓝 (L.toReal * ∫ x in (0 : ℝ)..1, p.eval x)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have hint : ∫ x in (0 : ℝ)..1, (p + q).eval x =
        (∫ x in (0 : ℝ)..1, p.eval x) + ∫ x in (0 : ℝ)..1, q.eval x := by
      simp only [Polynomial.eval_add]
      exact intervalIntegral.integral_add (p.continuous.intervalIntegrable _ _)
        (q.continuous.intervalIntegrable _ _)
    rw [hint, mul_add]
    refine (hp.add hq).congr' ?_
    filter_upwards [bwReuse_abel_limit_continuous_alc_eventually_good u L hL hlim] with α hα
    simp only [Polynomial.eval_add]
    exact (bwReuse_abel_limit_continuous_alc_add u hα _ _ p.continuous.continuousOn q.continuous.continuousOn).symm
  | monomial n a =>
    simp only [Polynomial.eval_monomial]
    have hm := (bwReuse_abel_limit_continuous_alc_monomial u hu0 L hL hlim n).const_mul a
    rw [intervalIntegral.integral_const_mul]
    have : L.toReal * (a * ∫ x in (0 : ℝ)..1, x ^ n) = a * (L.toReal * ∫ x in (0 : ℝ)..1, x ^ n) :=
      by ring
    rw [this]
    refine hm.congr fun α => ?_
    exact (bwReuse_abel_limit_continuous_alc_smul u α (fun x => x ^ n) a).symm

theorem bwReuse_abel_limit_continuous_alc_abs_le (u : ℕ → ℝ≥0∞) {α : ℝ≥0} (h : bwReuse_abel_limit_continuous_alcGood u α) (g : ℝ → ℝ) (ε : ℝ)
    (hg : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x| ≤ ε) :
    |bwReuse_abel_limit_continuous_alcAr u g α| ≤ ε * bwReuse_abel_limit_continuous_alcAr u (fun _ => 1) α := by
  unfold bwReuse_abel_limit_continuous_alcAr
  have h1 : 0 ≤ 1 - (α : ℝ) := by
    have : (α : ℝ) < 1 := by exact_mod_cast h.2.1
    linarith
  have hs := bwReuse_abel_limit_continuous_alc_summable_of_bound h g ε hg
  have hsn : Summable (fun n : ℕ => ‖(α : ℝ) ^ n * (u n).toReal * g ((α : ℝ) ^ n)‖) := hs.norm
  rw [abs_mul, abs_of_nonneg h1]
  have : |∑' n : ℕ, (α : ℝ) ^ n * (u n).toReal * g ((α : ℝ) ^ n)| ≤
      ε * ∑' n : ℕ, (α : ℝ) ^ n * (u n).toReal * 1 := by
    calc |∑' n : ℕ, (α : ℝ) ^ n * (u n).toReal * g ((α : ℝ) ^ n)|
        ≤ ∑' n : ℕ, ‖(α : ℝ) ^ n * (u n).toReal * g ((α : ℝ) ^ n)‖ := by
          rw [← Real.norm_eq_abs]; exact norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' n : ℕ, ε * ((α : ℝ) ^ n * (u n).toReal * 1) := by
          refine hsn.tsum_le_tsum (fun n => ?_) ((bwReuse_abel_limit_continuous_alcGood_summable h).mul_left ε |>.congr
            fun n => by ring)
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
          have := hg _ (bwReuse_abel_limit_continuous_alcGood_mem h.2.1 n)
          nlinarith [show (0 : ℝ) ≤ (α : ℝ) ^ n * (u n).toReal by positivity]
      _ = ε * ∑' n : ℕ, (α : ℝ) ^ n * (u n).toReal * 1 := tsum_mul_left
  calc (1 - (α : ℝ)) * |∑' n : ℕ, (α : ℝ) ^ n * (u n).toReal * g ((α : ℝ) ^ n)|
      ≤ (1 - (α : ℝ)) * (ε * ∑' n : ℕ, (α : ℝ) ^ n * (u n).toReal * 1) :=
        mul_le_mul_of_nonneg_left this h1
    _ = _ := by ring

theorem bwReuse_abel_limit_continuous_alc_main (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1)) :
    Tendsto (bwReuse_abel_limit_continuous_alcAr u f) (𝓝[<] (1 : ℝ≥0)) (𝓝 (L.toReal * ∫ x in (0 : ℝ)..1, f x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set ℓ := L.toReal
  have hℓ : 0 ≤ ℓ := ENNReal.toReal_nonneg
  set δ := ε / (4 * (ℓ + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 f hf δ hδpos
  have hpoly := bwReuse_abel_limit_continuous_alc_poly u hu0 L hL hlim p
  have e1 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0),
      dist (bwReuse_abel_limit_continuous_alcAr u (fun x => p.eval x) α) (ℓ * ∫ x in (0 : ℝ)..1, p.eval x) < ε / 4 :=
    Metric.tendsto_nhds.mp hpoly (ε / 4) (by positivity)
  have e2 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), bwReuse_abel_limit_continuous_alcAr u (fun _ => 1) α < ℓ + 1 :=
    (bwReuse_abel_limit_continuous_alc_one u L hL hlim).eventually (gt_mem_nhds (by linarith))
  set If := ∫ x in (0 : ℝ)..1, f x with hIf
  set Ip := ∫ x in (0 : ℝ)..1, p.eval x with hIp
  have hI : |If - Ip| ≤ δ := by
    rw [hIf, hIp, ← intervalIntegral.integral_sub (hf.intervalIntegrable_of_Icc zero_le_one)
      (p.continuous.intervalIntegrable _ _)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (f := fun x => f x - p.eval x) (C := δ) (fun x hx => by
        rw [Set.uIoc_of_le zero_le_one] at hx
        rw [Real.norm_eq_abs, abs_sub_comm]
        exact (hp x ⟨hx.1.le, hx.2⟩).le)
    simpa using this
  have hint : |ℓ * If - ℓ * Ip| ≤ ℓ * δ := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hℓ]
    exact mul_le_mul_of_nonneg_left hI hℓ
  filter_upwards [e1, e2, bwReuse_abel_limit_continuous_alc_eventually_good u L hL hlim] with α a1 a2 hα
  have hdiff : |bwReuse_abel_limit_continuous_alcAr u f α - bwReuse_abel_limit_continuous_alcAr u (fun x => p.eval x) α| ≤ δ * bwReuse_abel_limit_continuous_alcAr u (fun _ => 1) α := by
    have hsplit := bwReuse_abel_limit_continuous_alc_add u hα (fun x => f x - p.eval x) (fun x => p.eval x)
      (hf.sub p.continuous.continuousOn) p.continuous.continuousOn
    simp only [sub_add_cancel] at hsplit
    rw [hsplit, add_sub_cancel_right]
    exact bwReuse_abel_limit_continuous_alc_abs_le u hα _ δ fun x hx => by rw [abs_sub_comm]; exact (hp x hx).le
  have hone_nn : 0 ≤ bwReuse_abel_limit_continuous_alcAr u (fun _ => 1) α := by
    have := bwReuse_abel_limit_continuous_alc_abs_le u hα (fun _ => 0) 0 (by simp)
    have h1 : (0 : ℝ) ≤ 1 - (α : ℝ) := by
      have : (α : ℝ) < 1 := by exact_mod_cast hα.2.1
      linarith
    unfold bwReuse_abel_limit_continuous_alcAr
    exact mul_nonneg h1 (tsum_nonneg fun n => by positivity)
  rw [Real.dist_eq] at a1 ⊢
  have hδmul : δ * (ℓ + 1) = ε / 4 := by
    rw [hδ]; field_simp
  have hb1 : δ * bwReuse_abel_limit_continuous_alcAr u (fun _ => 1) α ≤ ε / 4 := by
    rw [← hδmul]; exact mul_le_mul_of_nonneg_left a2.le hδpos.le
  have hb2 : ℓ * δ ≤ ε / 4 := by
    rw [← hδmul]; nlinarith
  have k1 := abs_le.mp (hdiff.trans hb1)
  have k2 := abs_le.mp a1.le
  have k3 := abs_le.mp (hint.trans hb2)
  have k4 := abs_lt.mp a1
  rw [abs_sub_lt_iff]
  constructor <;> linarith [k1.1, k1.2, k3.1, k3.2, k4.1, k4.2]

end SennottDP.Tauberian

open SennottDP.Tauberian in
theorem _root_.SennottDP.Tauberian.abel_limit_continuous (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1)) :
    Tendsto (fun α : ℝ≥0 =>
        (1 - (α : ℝ)) * ∑' n : ℕ, (α : ℝ) ^ n * (u n).toReal * f ((α : ℝ) ^ n))
      (𝓝[<] (1 : ℝ≥0)) (𝓝 (L.toReal * ∫ x in (0 : ℝ)..1, f x)) :=
  bwReuse_abel_limit_continuous_alc_main u hu0 L hL hlim f hf




open scoped ENNReal NNReal Topology
open Filter

set_option autoImplicit false

namespace SennottSandwichAux

/-- clipped ramp: `min (max x a)⁻¹ (K * max 0 (x - b))`. -/
noncomputable def bwReuse_continuous_sandwich_r_f (a b K : ℝ) (x : ℝ) : ℝ := min (max x a)⁻¹ (K * max 0 (x - b))

lemma bwReuse_continuous_sandwich_r_f_cont {a b K : ℝ} (ha : 0 < a) : Continuous (bwReuse_continuous_sandwich_r_f a b K) := by
  unfold bwReuse_continuous_sandwich_r_f
  apply Continuous.min
  · exact (continuous_id.max continuous_const).inv₀
      (fun x => (lt_of_lt_of_le ha (le_max_right x a)).ne')
  · exact continuous_const.mul (continuous_const.max (continuous_id.sub continuous_const))

lemma bwReuse_continuous_sandwich_r_f_nonneg {a b K x : ℝ} (ha : 0 < a) (hK : 0 ≤ K) : 0 ≤ bwReuse_continuous_sandwich_r_f a b K x := by
  unfold bwReuse_continuous_sandwich_r_f
  apply le_min
  · exact inv_nonneg.mpr (le_trans ha.le (le_max_right _ _))
  · exact mul_nonneg hK (le_max_left _ _)

lemma bwReuse_continuous_sandwich_r_f_le_inv {a b K x : ℝ} (hx : a ≤ x) : bwReuse_continuous_sandwich_r_f a b K x ≤ x⁻¹ := by
  unfold bwReuse_continuous_sandwich_r_f
  rw [max_eq_left hx]
  exact min_le_left _ _

lemma bwReuse_continuous_sandwich_r_f_le_ramp {a b K x : ℝ} (hK : 0 ≤ K) (hxb : b ≤ x) : bwReuse_continuous_sandwich_r_f a b K x ≤ K * (x - b) := by
  unfold bwReuse_continuous_sandwich_r_f
  rw [max_eq_right (sub_nonneg.mpr hxb)]
  exact min_le_right _ _

lemma bwReuse_continuous_sandwich_r_f_eq_zero {a b K x : ℝ} (ha : 0 < a) (hx : x ≤ b) : bwReuse_continuous_sandwich_r_f a b K x = 0 := by
  unfold bwReuse_continuous_sandwich_r_f
  have : max 0 (x - b) = 0 := max_eq_left (by linarith)
  rw [this, mul_zero]
  exact min_eq_right (inv_nonneg.mpr (le_trans ha.le (le_max_right _ _)))

lemma bwReuse_continuous_sandwich_r_f_eq_inv {a b K x : ℝ} (hx : a ≤ x) (hxb : b ≤ x) (h : x⁻¹ ≤ K * (x - b)) :
    bwReuse_continuous_sandwich_r_f a b K x = x⁻¹ := by
  unfold bwReuse_continuous_sandwich_r_f
  rw [max_eq_left hx, max_eq_right (sub_nonneg.mpr hxb)]
  exact min_eq_left h

lemma bwReuse_continuous_sandwich_r_exp_neg_one_inv : (Real.exp (-1))⁻¹ = Real.exp 1 := by
  rw [Real.exp_neg, inv_inv]

end SennottSandwichAux

open SennottSandwichAux in
open SennottDP.Tauberian in
theorem _root_.SennottDP.Tauberian.continuous_sandwich_r (ε : ℝ) (hε : 0 < ε) :
    ∃ s sstar : ℝ → ℝ, ContinuousOn s (Set.Icc 0 1) ∧ ContinuousOn sstar (Set.Icc 0 1) ∧
      (∀ x ∈ Set.Ioo (0 : ℝ) 1, sstar x ≤ r x ∧ r x ≤ s x) ∧
      1 - ε ≤ ∫ x in (0 : ℝ)..1, sstar x ∧
      ∫ x in (0 : ℝ)..1, sstar x ≤ ∫ x in (0 : ℝ)..1, s x ∧
      ∫ x in (0 : ℝ)..1, s x ≤ 1 + ε := by
  set a : ℝ := Real.exp (-1) with ha_def
  set b : ℝ := Real.exp (-1 - ε) with hb_def
  set c : ℝ := Real.exp (-1 + min ε 1) with hc_def
  have ha : 0 < a := Real.exp_pos _
  have hb : 0 < b := Real.exp_pos _
  have hc : 0 < c := Real.exp_pos _
  have hm : 0 < min ε 1 := lt_min hε one_pos
  have hba : b < a := Real.exp_lt_exp.mpr (by linarith)
  have hac : a < c := Real.exp_lt_exp.mpr (by linarith)
  have hc1 : c ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [min_le_right ε 1])
  have hb1 : b ≤ 1 := le_trans hba.le (le_trans hac.le hc1)
  have hainv : a⁻¹ = Real.exp 1 := bwReuse_continuous_sandwich_r_exp_neg_one_inv
  set K₁ : ℝ := Real.exp 1 / (a - b) with hK₁
  set K₂ : ℝ := Real.exp 1 / (c - a) with hK₂
  have hK₁0 : 0 ≤ K₁ := div_nonneg (Real.exp_pos 1).le (by linarith)
  have hK₂0 : 0 ≤ K₂ := div_nonneg (Real.exp_pos 1).le (by linarith)
  have hK₁e : K₁ * (a - b) = Real.exp 1 := div_mul_cancel₀ _ (by linarith)
  have hK₂e : K₂ * (c - a) = Real.exp 1 := div_mul_cancel₀ _ (by linarith)
  -- x⁻¹ ≤ exp 1 for x ≥ a
  have hinv_le : ∀ x : ℝ, a ≤ x → x⁻¹ ≤ Real.exp 1 := by
    intro x hx
    rw [← hainv]
    exact inv_anti₀ ha hx
  let s : ℝ → ℝ := bwReuse_continuous_sandwich_r_f a b K₁
  let sstar : ℝ → ℝ := bwReuse_continuous_sandwich_r_f a a K₂
  have s_eq : ∀ x, a ≤ x → s x = x⁻¹ := by
    intro x hx
    apply bwReuse_continuous_sandwich_r_f_eq_inv hx (le_trans hba.le hx)
    calc x⁻¹ ≤ Real.exp 1 := hinv_le x hx
      _ = K₁ * (a - b) := hK₁e.symm
      _ ≤ K₁ * (x - b) := mul_le_mul_of_nonneg_left (by linarith) hK₁0
  have sstar_eq : ∀ x, c ≤ x → sstar x = x⁻¹ := by
    intro x hx
    apply bwReuse_continuous_sandwich_r_f_eq_inv (le_trans hac.le hx) (le_trans hac.le hx)
    calc x⁻¹ ≤ Real.exp 1 := hinv_le x (le_trans hac.le hx)
      _ = K₂ * (c - a) := hK₂e.symm
      _ ≤ K₂ * (x - a) := mul_le_mul_of_nonneg_left (by linarith) hK₂0
  have s_le_inv : ∀ x, b ≤ x → s x ≤ x⁻¹ := by
    intro x hx
    by_cases hax : a ≤ x
    · exact bwReuse_continuous_sandwich_r_f_le_inv hax
    · push_neg at hax
      calc s x ≤ K₁ * (x - b) := bwReuse_continuous_sandwich_r_f_le_ramp hK₁0 hx
        _ ≤ K₁ * (a - b) := mul_le_mul_of_nonneg_left (by linarith) hK₁0
        _ = a⁻¹ := by rw [hK₁e, hainv]
        _ ≤ x⁻¹ := inv_anti₀ (lt_of_lt_of_le hb hx) hax.le
  have sstar_le_r : ∀ x, sstar x ≤ r x := by
    intro x
    unfold r
    split_ifs with hx
    · exact bwReuse_continuous_sandwich_r_f_le_inv hx
    · push_neg at hx
      exact (bwReuse_continuous_sandwich_r_f_eq_zero ha hx.le).le
  have r_le_s : ∀ x, r x ≤ s x := by
    intro x
    unfold r
    split_ifs with hx
    · exact (s_eq x hx).ge
    · exact bwReuse_continuous_sandwich_r_f_nonneg ha hK₁0
  have sstar_le_s : ∀ x, sstar x ≤ s x := fun x => le_trans (sstar_le_r x) (r_le_s x)
  have hs_cont : Continuous s := bwReuse_continuous_sandwich_r_f_cont ha
  have hss_cont : Continuous sstar := bwReuse_continuous_sandwich_r_f_cont ha
  have hinv_int : ∀ u v : ℝ, 0 < u → 0 < v →
      IntervalIntegrable (fun x : ℝ => x⁻¹) MeasureTheory.volume u v := by
    intro u v hu hv
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_inv₀.mono
    intro x hx
    rw [Set.mem_uIcc] at hx
    have : 0 < x := by rcases hx with h | h <;> linarith [h.1]
    exact this.ne'
  refine ⟨s, sstar, hs_cont.continuousOn, hss_cont.continuousOn,
    fun x _ => ⟨sstar_le_r x, r_le_s x⟩, ?_, ?_, ?_⟩
  · have h1 : ∫ x in (0:ℝ)..1, sstar x = (∫ x in (0:ℝ)..c, sstar x) + ∫ x in c..1, sstar x :=
      (intervalIntegral.integral_add_adjacent_intervals (hss_cont.intervalIntegrable _ _)
        (hss_cont.intervalIntegrable _ _)).symm
    have h2 : 0 ≤ ∫ x in (0:ℝ)..c, sstar x :=
      intervalIntegral.integral_nonneg hc.le (fun x _ => bwReuse_continuous_sandwich_r_f_nonneg ha hK₂0)
    have h3 : ∫ x in c..1, sstar x = ∫ x in c..1, x⁻¹ := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hc1] at hx
      exact sstar_eq x hx.1
    have h4 : ∫ x in c..1, x⁻¹ = 1 - min ε 1 := by
      rw [integral_inv_of_pos hc one_pos, one_div, Real.log_inv, hc_def, Real.log_exp]
      ring
    rw [h1, h3, h4]
    linarith [min_le_left ε 1]
  · exact intervalIntegral.integral_mono_on zero_le_one (hss_cont.intervalIntegrable _ _)
      (hs_cont.intervalIntegrable _ _) (fun x _ => sstar_le_s x)
  · have h1 : ∫ x in (0:ℝ)..1, s x = (∫ x in (0:ℝ)..b, s x) + ∫ x in b..1, s x :=
      (intervalIntegral.integral_add_adjacent_intervals (hs_cont.intervalIntegrable _ _)
        (hs_cont.intervalIntegrable _ _)).symm
    have h2 : ∫ x in (0:ℝ)..b, s x = 0 := by
      have : ∫ x in (0:ℝ)..b, s x = ∫ x in (0:ℝ)..b, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hb.le] at hx
        exact bwReuse_continuous_sandwich_r_f_eq_zero ha hx.2
      rw [this, intervalIntegral.integral_zero]
    have h3 : ∫ x in b..1, s x ≤ ∫ x in b..1, x⁻¹ :=
      intervalIntegral.integral_mono_on hb1 (hs_cont.intervalIntegrable _ _)
        (hinv_int b 1 hb one_pos) (fun x hx => s_le_inv x hx.1)
    have h4 : ∫ x in b..1, x⁻¹ = 1 + ε := by
      rw [integral_inv_of_pos hb one_pos, one_div, Real.log_inv, hb_def, Real.log_exp]
      ring
    rw [h1, h2, zero_add]
    linarith


open scoped ENNReal NNReal Topology
open Filter

open SennottDP.Tauberian in
theorem _root_.SennottDP.Tauberian.integral_r :
    ∫ x in (0 : ℝ)..1, r x = ∫ x in Real.exp (-1)..1, x⁻¹ ∧
      ∫ x in Real.exp (-1)..1, x⁻¹ = 1 := by
  set a := Real.exp (-1) with ha
  have ha0 : 0 < a := Real.exp_pos _
  have ha1 : a ≤ 1 := by
    rw [ha]; exact Real.exp_le_one_iff.mpr (by norm_num)
  have e1 : Set.EqOn (fun _ : ℝ => (0 : ℝ)) r (Set.uIoo 0 a) := by
    intro x hx
    rw [Set.uIoo_of_le ha0.le] at hx
    simp only [r]
    rw [if_neg (not_le.mpr (by rw [← ha]; exact hx.2))]
  have i1 : IntervalIntegrable r MeasureTheory.volume 0 a :=
    (intervalIntegrable_const (c := (0 : ℝ))).congr_uIoo e1
  have e2 : Set.EqOn (fun x : ℝ => x⁻¹) r (Set.uIcc a 1) := by
    intro x hx
    rw [Set.uIcc_of_le ha1] at hx
    simp only [r]
    rw [if_pos (by rw [← ha]; exact hx.1)]
  have c2 : ContinuousOn (fun x : ℝ => x⁻¹) (Set.uIcc a 1) := by
    apply continuousOn_inv₀.mono
    intro x hx
    rw [Set.uIcc_of_le ha1] at hx
    exact ne_of_gt (lt_of_lt_of_le ha0 hx.1)
  have i2 : IntervalIntegrable r MeasureTheory.volume a 1 :=
    c2.intervalIntegrable.congr (e2.mono Set.uIoc_subset_uIcc)
  have p1 : ∫ x in (0:ℝ)..a, r x = 0 := by
    rw [← intervalIntegral.integral_congr_uIoo e1]; simp
  have p2 : ∫ x in a..1, r x = ∫ x in a..1, x⁻¹ :=
    (intervalIntegral.integral_congr e2).symm
  refine ⟨?_, ?_⟩
  · rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2, p1, p2, zero_add]
  · rw [integral_inv_of_pos ha0 one_pos, ha, one_div, ← Real.exp_neg, neg_neg, Real.log_exp]


open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian

/-- The real Abel-type mean `(1-α) ∑ α^n u_n g(α^n)`. -/
noncomputable def bwReuse_abel_limit_r_alcAr (u : ℕ → ℝ≥0∞) (g : ℝ → ℝ) (α : ℝ≥0) : ℝ :=
  (1 - (α : ℝ)) * ∑' n : ℕ, (α : ℝ) ^ n * (u n).toReal * g ((α : ℝ) ^ n)

/-- "Good" parameters: `0 < α < 1` and `U(α) < ∞`. -/
def bwReuse_abel_limit_r_alcGood (u : ℕ → ℝ≥0∞) (α : ℝ≥0) : Prop :=
  0 < α ∧ α < 1 ∧ U u α ≠ ⊤

theorem bwReuse_abel_limit_r_alcGood_fin {u : ℕ → ℝ≥0∞} {α : ℝ≥0} (h : bwReuse_abel_limit_r_alcGood u α) (n : ℕ) : u n ≠ ⊤ := by
  obtain ⟨h0, -, hU⟩ := h
  have hle : (α : ℝ≥0∞) ^ n * u n ≤ U u α := ENNReal.le_tsum (f := fun n => (α : ℝ≥0∞) ^ n * u n) n
  have hne : (α : ℝ≥0∞) ^ n * u n ≠ ⊤ := ne_top_of_le_ne_top hU hle
  intro hu
  apply hne
  rw [hu]
  exact ENNReal.mul_top (pow_ne_zero _ (by exact_mod_cast h0.ne'))

theorem bwReuse_abel_limit_r_alcGood_summable {u : ℕ → ℝ≥0∞} {α : ℝ≥0} (h : bwReuse_abel_limit_r_alcGood u α) :
    Summable (fun n : ℕ => (α : ℝ) ^ n * (u n).toReal) := by
  have := ENNReal.summable_toReal h.2.2
  refine this.congr fun n => ?_
  simp [ENNReal.toReal_mul, ENNReal.toReal_pow]

theorem bwReuse_abel_limit_r_alcGood_tsum {u : ℕ → ℝ≥0∞} {α : ℝ≥0} (h : bwReuse_abel_limit_r_alcGood u α) (k : ℕ) :
    (∑' n : ℕ, (α : ℝ≥0∞) ^ n * u n * ((α : ℝ≥0∞) ^ n) ^ k).toReal =
      ∑' n : ℕ, (α : ℝ) ^ n * (u n).toReal * ((α : ℝ) ^ n) ^ k := by
  rw [ENNReal.tsum_toReal_eq]
  · refine tsum_congr fun n => ?_
    simp [ENNReal.toReal_mul, ENNReal.toReal_pow]
  · intro n
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      (bwReuse_abel_limit_r_alcGood_fin h n)) (ENNReal.pow_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top))

theorem bwReuse_abel_limit_r_alcGood_one_sub {α : ℝ≥0} (h : α < 1) : (1 - (α : ℝ≥0∞)).toReal = 1 - (α : ℝ) := by
  rw [ENNReal.toReal_sub_of_le (by exact_mod_cast h.le) ENNReal.one_ne_top]
  simp

theorem bwReuse_abel_limit_r_alcGood_mem {α : ℝ≥0} (h : α < 1) (n : ℕ) : (α : ℝ) ^ n ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨by positivity, pow_le_one₀ (by positivity) (by exact_mod_cast h.le)⟩

theorem bwReuse_abel_limit_r_alc_summable_of_bound {u : ℕ → ℝ≥0∞} {α : ℝ≥0} (h : bwReuse_abel_limit_r_alcGood u α) (g : ℝ → ℝ) (B : ℝ)
    (hB : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x| ≤ B) :
    Summable (fun n : ℕ => (α : ℝ) ^ n * (u n).toReal * g ((α : ℝ) ^ n)) := by
  refine Summable.of_norm_bounded ((bwReuse_abel_limit_r_alcGood_summable h).mul_right B) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (hB _ (bwReuse_abel_limit_r_alcGood_mem h.2.1 n)) (by positivity)

theorem bwReuse_abel_limit_r_alc_bound_of_contOn (g : ℝ → ℝ) (hg : ContinuousOn g (Set.Icc 0 1)) :
    ∃ B : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  exact ⟨B, fun x hx => by simpa [Real.norm_eq_abs] using hB x hx⟩

theorem bwReuse_abel_limit_r_alc_eventually_good (u : ℕ → ℝ≥0∞) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) :
    ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), bwReuse_abel_limit_r_alcGood u α := by
  have h1 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), α < 1 := self_mem_nhdsWithin
  have h2 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), 0 < α :=
    nhdsWithin_le_nhds (lt_mem_nhds (zero_lt_one : (0 : ℝ≥0) < 1))
  have h3 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), abelMean u α < L + 1 :=
    hlim.eventually (gt_mem_nhds (ENNReal.lt_add_right hL one_ne_zero))
  filter_upwards [h1, h2, h3] with α a1 a2 a3
  refine ⟨a2, a1, ?_⟩
  have hα' : (α : ℝ≥0∞) < 1 := by exact_mod_cast a1
  have h0 : (1 - (α : ℝ≥0∞)) ≠ 0 := (tsub_pos_of_lt hα').ne'
  have hfin : abelMean u α ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le a3 le_top) |>.symm.symm
  · intro hU
    apply (lt_of_lt_of_le a3 le_top).ne
    unfold abelMean
    rw [hU, ENNReal.mul_top h0]

theorem bwReuse_abel_limit_r_alc_one (u : ℕ → ℝ≥0∞) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) :
    Tendsto (bwReuse_abel_limit_r_alcAr u (fun _ => 1)) (𝓝[<] (1 : ℝ≥0)) (𝓝 L.toReal) := by
  have ht := (ENNReal.tendsto_toReal hL).comp hlim
  refine ht.congr' ?_
  filter_upwards [bwReuse_abel_limit_r_alc_eventually_good u L hL hlim] with α hα
  simp only [Function.comp, bwReuse_abel_limit_r_alcAr, abelMean, U]
  rw [ENNReal.toReal_mul, bwReuse_abel_limit_r_alcGood_one_sub hα.2.1]
  have := bwReuse_abel_limit_r_alcGood_tsum hα 0
  simp only [pow_zero, mul_one] at this
  rw [this]
  simp


theorem bwReuse_abel_limit_r_alr_r_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ r x := by
  unfold r; split_ifs <;> positivity

theorem bwReuse_abel_limit_r_alr_r_bound (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : |r x| ≤ Real.exp 1 := by
  rw [abs_of_nonneg (bwReuse_abel_limit_r_alr_r_nonneg x hx.1)]
  unfold r
  split_ifs with h
  · have hpos : 0 < Real.exp (-1) := Real.exp_pos _
    calc x⁻¹ ≤ (Real.exp (-1))⁻¹ := inv_anti₀ hpos h
      _ = Real.exp 1 := by rw [Real.exp_neg, inv_inv]
  · exact (Real.exp_pos 1).le

theorem bwReuse_abel_limit_r_alr_r_one : r 1 = 1 := by
  unfold r
  rw [if_pos (by rw [Real.exp_le_one_iff]; norm_num), inv_one]

theorem bwReuse_abel_limit_r_alr_sub (u : ℕ → ℝ≥0∞) {α : ℝ≥0} (h : bwReuse_abel_limit_r_alcGood u α) (g₁ g₂ : ℝ → ℝ) (B₁ B₂ : ℝ)
    (h₁ : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g₁ x| ≤ B₁) (h₂ : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g₂ x| ≤ B₂) :
    bwReuse_abel_limit_r_alcAr u (fun x => g₁ x - g₂ x) α = bwReuse_abel_limit_r_alcAr u g₁ α - bwReuse_abel_limit_r_alcAr u g₂ α := by
  unfold bwReuse_abel_limit_r_alcAr
  rw [← mul_sub, ← (bwReuse_abel_limit_r_alc_summable_of_bound h g₁ B₁ h₁).tsum_sub
    (bwReuse_abel_limit_r_alc_summable_of_bound h g₂ B₂ h₂)]
  congr 1
  exact tsum_congr fun n => by ring

theorem bwReuse_abel_limit_r_alr_le_head (u : ℕ → ℝ≥0∞) {α : ℝ≥0} (h : bwReuse_abel_limit_r_alcGood u α) (g : ℝ → ℝ) (B : ℝ)
    (hB : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x| ≤ B) (hneg : ∀ x ∈ Set.Ioo (0 : ℝ) 1, g x ≤ 0) :
    bwReuse_abel_limit_r_alcAr u g α ≤ (1 - (α : ℝ)) * ((u 0).toReal * g 1) := by
  unfold bwReuse_abel_limit_r_alcAr
  have h1 : 0 ≤ 1 - (α : ℝ) := by
    have : (α : ℝ) < 1 := by exact_mod_cast h.2.1
    linarith
  refine mul_le_mul_of_nonneg_left ?_ h1
  rw [(bwReuse_abel_limit_r_alc_summable_of_bound h g B hB).tsum_eq_zero_add]
  simp only [pow_zero, one_mul]
  have : ∑' n : ℕ, (α : ℝ) ^ (n + 1) * (u (n + 1)).toReal * g ((α : ℝ) ^ (n + 1)) ≤ 0 := by
    refine tsum_nonpos fun n => ?_
    have hα0 : (0 : ℝ) < α := by exact_mod_cast h.1
    have hα1 : (α : ℝ) < 1 := by exact_mod_cast h.2.1
    have hmem : (α : ℝ) ^ (n + 1) ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨by positivity, pow_lt_one₀ hα0.le hα1 (by omega)⟩
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hneg _ hmem)
  linarith

theorem bwReuse_abel_limit_r_alr_tendsto_zero (K : ℝ) :
    Tendsto (fun α : ℝ≥0 => (1 - (α : ℝ)) * K) (𝓝[<] (1 : ℝ≥0)) (𝓝 0) := by
  have : Tendsto (fun α : ℝ≥0 => (1 - (α : ℝ)) * K) (𝓝 (1 : ℝ≥0)) (𝓝 ((1 - ((1 : ℝ≥0) : ℝ)) * K)) :=
    ((continuous_const.sub NNReal.continuous_coe).mul continuous_const).tendsto 1
  simp only [NNReal.coe_one, sub_self, zero_mul] at this
  exact this.mono_left nhdsWithin_le_nhds

theorem bwReuse_abel_limit_r_alr_real (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) :
    Tendsto (bwReuse_abel_limit_r_alcAr u r) (𝓝[<] (1 : ℝ≥0)) (𝓝 L.toReal) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set ℓ := L.toReal
  have hℓ : 0 ≤ ℓ := ENNReal.toReal_nonneg
  set ε1 := ε / (4 * (ℓ + 1)) with hε1
  have hε1pos : 0 < ε1 := by positivity
  have hℓε1 : ℓ * ε1 ≤ ε / 4 := by
    have : ε1 * (ℓ + 1) = ε / 4 := by rw [hε1]; field_simp
    nlinarith
  obtain ⟨s, ss, hs, hss, hsr, hI1, -, hI3⟩ := continuous_sandwich_r ε1 hε1pos
  obtain ⟨Bs, hBs⟩ := bwReuse_abel_limit_r_alc_bound_of_contOn s hs
  obtain ⟨Bss, hBss⟩ := bwReuse_abel_limit_r_alc_bound_of_contOn ss hss
  have ts := abel_limit_continuous u hu0 L hL hlim s hs
  have tss := abel_limit_continuous u hu0 L hL hlim ss hss
  have e1 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), bwReuse_abel_limit_r_alcAr u s α < ℓ * (∫ x in (0 : ℝ)..1, s x) + ε / 4 :=
    ts.eventually (gt_mem_nhds (by linarith))
  have e2 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), ℓ * (∫ x in (0 : ℝ)..1, ss x) - ε / 4 < bwReuse_abel_limit_r_alcAr u ss α :=
    tss.eventually (lt_mem_nhds (by linarith))
  have e3 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0),
      (1 - (α : ℝ)) * ((u 0).toReal * |r 1 - s 1|) < ε / 4 :=
    (bwReuse_abel_limit_r_alr_tendsto_zero _).eventually (gt_mem_nhds (by positivity))
  have e4 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0),
      (1 - (α : ℝ)) * ((u 0).toReal * |ss 1 - r 1|) < ε / 4 :=
    (bwReuse_abel_limit_r_alr_tendsto_zero _).eventually (gt_mem_nhds (by positivity))
  filter_upwards [e1, e2, e3, e4, bwReuse_abel_limit_r_alc_eventually_good u L hL hlim] with α a1 a2 a3 a4 hα
  have h1 : 0 ≤ 1 - (α : ℝ) := by
    have : (α : ℝ) < 1 := by exact_mod_cast hα.2.1
    linarith
  have hu0' : 0 ≤ (u 0).toReal := ENNReal.toReal_nonneg
  -- upper
  have up := bwReuse_abel_limit_r_alr_le_head u hα (fun x => r x - s x) (Real.exp 1 + Bs)
    (fun x hx => (abs_sub _ _).trans (add_le_add (bwReuse_abel_limit_r_alr_r_bound x hx) (hBs x hx)))
    (fun x hx => sub_nonpos.mpr (hsr x hx).2)
  rw [bwReuse_abel_limit_r_alr_sub u hα r s _ _ bwReuse_abel_limit_r_alr_r_bound hBs] at up
  have up2 : (1 - (α : ℝ)) * ((u 0).toReal * (r 1 - s 1)) ≤
      (1 - (α : ℝ)) * ((u 0).toReal * |r 1 - s 1|) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_abs_self _) hu0') h1
  -- lower
  have lo := bwReuse_abel_limit_r_alr_le_head u hα (fun x => ss x - r x) (Bss + Real.exp 1)
    (fun x hx => (abs_sub _ _).trans (add_le_add (hBss x hx) (bwReuse_abel_limit_r_alr_r_bound x hx)))
    (fun x hx => sub_nonpos.mpr (hsr x hx).1)
  rw [bwReuse_abel_limit_r_alr_sub u hα ss r _ _ hBss bwReuse_abel_limit_r_alr_r_bound] at lo
  have lo2 : (1 - (α : ℝ)) * ((u 0).toReal * (ss 1 - r 1)) ≤
      (1 - (α : ℝ)) * ((u 0).toReal * |ss 1 - r 1|) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_abs_self _) hu0') h1
  have i1 : ℓ * (∫ x in (0 : ℝ)..1, s x) ≤ ℓ * (1 + ε1) := mul_le_mul_of_nonneg_left hI3 hℓ
  have i2 : ℓ * (1 - ε1) ≤ ℓ * (∫ x in (0 : ℝ)..1, ss x) := mul_le_mul_of_nonneg_left hI1 hℓ
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> nlinarith

end SennottDP.Tauberian

open SennottDP.Tauberian in
theorem _root_.SennottDP.Tauberian.abel_limit_r (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) :
    Tendsto (fun α : ℝ≥0 =>
        (1 - (α : ℝ≥0∞)) * ∑' n : ℕ, (α : ℝ≥0∞) ^ n * u n * ENNReal.ofReal (r ((α : ℝ) ^ n)))
      (𝓝[<] (1 : ℝ≥0)) (𝓝 (L * ENNReal.ofReal (∫ x in (0 : ℝ)..1, r x))) := by
  have hI : ∫ x in (0 : ℝ)..1, r x = 1 := integral_r.1.trans integral_r.2
  rw [hI, ENNReal.ofReal_one, mul_one]
  have ht := ENNReal.tendsto_ofReal (bwReuse_abel_limit_r_alr_real u hu0 L hL hlim)
  rw [ENNReal.ofReal_toReal hL] at ht
  refine ht.congr' ?_
  filter_upwards [bwReuse_abel_limit_r_alc_eventually_good u L hL hlim] with α hα
  have h1 : 0 ≤ 1 - (α : ℝ) := by
    have : (α : ℝ) < 1 := by exact_mod_cast hα.2.1
    linarith
  unfold bwReuse_abel_limit_r_alcAr
  rw [ENNReal.ofReal_mul h1]
  have hsub : ENNReal.ofReal (1 - (α : ℝ)) = 1 - (α : ℝ≥0∞) := by
    rw [← NNReal.coe_one, ← NNReal.coe_sub hα.2.1.le, ENNReal.ofReal_coe_nnreal,
      ENNReal.coe_sub, ENNReal.coe_one]
  rw [hsub]
  congr 1
  · rw [ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (by positivity)
      (bwReuse_abel_limit_r_alr_r_nonneg _ (by positivity))) (bwReuse_abel_limit_r_alc_summable_of_bound hα r _ bwReuse_abel_limit_r_alr_r_bound)]
    refine tsum_congr fun n => ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_toReal (bwReuse_abel_limit_r_alcGood_fin hα n), ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_coe_nnreal]




open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian

/-- `a_N = exp(-1/(N+1))`. -/
noncomputable def bwReuse_tauberian_theorem_ttA (N : ℕ) : ℝ≥0 :=
  ⟨Real.exp (-(1 / ((N : ℝ) + 1))), (Real.exp_pos _).le⟩

theorem bwReuse_tauberian_theorem_ttA_coe (N : ℕ) : ((bwReuse_tauberian_theorem_ttA N : ℝ≥0) : ℝ) = Real.exp (-(1 / ((N : ℝ) + 1))) := rfl

theorem bwReuse_tauberian_theorem_ttA_lt_one (N : ℕ) : bwReuse_tauberian_theorem_ttA N < 1 := by
  rw [← NNReal.coe_lt_coe, bwReuse_tauberian_theorem_ttA_coe, NNReal.coe_one]
  exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos (by positivity))

theorem bwReuse_tauberian_theorem_ttA_tendsto : Tendsto bwReuse_tauberian_theorem_ttA atTop (𝓝[<] (1 : ℝ≥0)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall bwReuse_tauberian_theorem_ttA_lt_one⟩
  rw [← NNReal.tendsto_coe]
  simp only [bwReuse_tauberian_theorem_ttA_coe, NNReal.coe_one]
  have h0 : Tendsto (fun N : ℕ => -(1 / ((N : ℝ) + 1))) atTop (𝓝 (-0)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.neg
  rw [neg_zero] at h0
  have := (Real.continuous_exp.tendsto 0).comp h0
  rw [Real.exp_zero] at this
  exact this

/-- The truncated sum: `∑ α^n u_n r(α^n) = w_{N+2}` at `α = a_N`. -/
theorem bwReuse_tauberian_theorem_tt_sum (u : ℕ → ℝ≥0∞) (N : ℕ) :
    ∑' n : ℕ, ((bwReuse_tauberian_theorem_ttA N : ℝ≥0) : ℝ≥0∞) ^ n * u n * ENNReal.ofReal (r (((bwReuse_tauberian_theorem_ttA N : ℝ≥0) : ℝ) ^ n))
      = w u (N + 2) := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hpow : ∀ n : ℕ, (((bwReuse_tauberian_theorem_ttA N : ℝ≥0) : ℝ)) ^ n = Real.exp (-((n : ℝ) / ((N : ℝ) + 1))) := by
    intro n
    rw [bwReuse_tauberian_theorem_ttA_coe, ← Real.exp_nat_mul]
    congr 1
    field_simp
  have hterm : ∀ n : ℕ, ((bwReuse_tauberian_theorem_ttA N : ℝ≥0) : ℝ≥0∞) ^ n * u n *
      ENNReal.ofReal (r (((bwReuse_tauberian_theorem_ttA N : ℝ≥0) : ℝ) ^ n)) = if n < N + 2 then u n else 0 := by
    intro n
    have hcoe : ((bwReuse_tauberian_theorem_ttA N : ℝ≥0) : ℝ≥0∞) ^ n = ENNReal.ofReal ((((bwReuse_tauberian_theorem_ttA N : ℝ≥0) : ℝ)) ^ n) := by
      rw [ENNReal.ofReal_pow NNReal.zero_le_coe, ENNReal.ofReal_coe_nnreal]
    rw [hcoe]
    unfold r
    rw [hpow]
    by_cases hn : n < N + 2
    · rw [if_pos hn, if_pos]
      · rw [mul_comm (ENNReal.ofReal _) (u n), mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          mul_inv_cancel₀ (Real.exp_pos _).ne', ENNReal.ofReal_one, mul_one]
      · rw [Real.exp_le_exp, neg_le_neg_iff, div_le_one hN]
        have : (n : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast (show n ≤ N + 1 by omega)
        exact this
    · rw [if_neg hn, if_neg, ENNReal.ofReal_zero, mul_zero]
      rw [Real.exp_le_exp, neg_le_neg_iff, div_le_one hN, not_le]
      exact_mod_cast (show N + 1 < n by omega)
  rw [tsum_congr hterm, tsum_eq_sum (s := Finset.range (N + 2))]
  · unfold w
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [if_pos (Finset.mem_range.mp hn)]
  · intro n hn
    rw [if_neg (fun h => hn (Finset.mem_range.mpr h))]

/-- `(N+2)(1 - a_N) → 1`. -/
theorem bwReuse_tauberian_theorem_tt_ratio :
    Tendsto (fun N : ℕ => (1 - ((bwReuse_tauberian_theorem_ttA N : ℝ≥0) : ℝ≥0∞)) * ((N : ℝ≥0∞) + 2)) atTop (𝓝 1) := by
  have heq : ∀ N : ℕ, (1 - ((bwReuse_tauberian_theorem_ttA N : ℝ≥0) : ℝ≥0∞)) * ((N : ℝ≥0∞) + 2) =
      ENNReal.ofReal ((1 - Real.exp (-(1 / ((N : ℝ) + 1)))) * ((N : ℝ) + 2)) := by
    intro N
    have hsub : ENNReal.ofReal (1 - ((bwReuse_tauberian_theorem_ttA N : ℝ≥0) : ℝ)) = 1 - ((bwReuse_tauberian_theorem_ttA N : ℝ≥0) : ℝ≥0∞) := by
      rw [← NNReal.coe_one, ← NNReal.coe_sub (bwReuse_tauberian_theorem_ttA_lt_one N).le, ENNReal.ofReal_coe_nnreal,
        ENNReal.coe_sub, ENNReal.coe_one]
    rw [ENNReal.ofReal_mul (by
      have := bwReuse_tauberian_theorem_ttA_lt_one N
      have : ((bwReuse_tauberian_theorem_ttA N : ℝ≥0) : ℝ) < 1 := by exact_mod_cast this
      rw [← bwReuse_tauberian_theorem_ttA_coe]; linarith), ← bwReuse_tauberian_theorem_ttA_coe, hsub]
    congr 1
    rw [ENNReal.ofReal_add (by positivity) (by norm_num)]
    simp
  simp_rw [heq]
  rw [← ENNReal.ofReal_one]
  refine ENNReal.tendsto_ofReal ?_
  have hup : Tendsto (fun N : ℕ => 1 + 1 / ((N : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
  rw [add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun N => ?_) (fun N => ?_)
  · -- lower bound: exp(-h) ≤ 1/(1+h)
    set h := 1 / ((N : ℝ) + 1) with hh
    have hpos : 0 < h := by positivity
    have h1 : Real.exp (-h) * (1 + h) ≤ 1 := by
      have := Real.add_one_le_exp h
      have he : Real.exp (-h) * Real.exp h = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-h)]
    have hN2 : (N : ℝ) + 2 = (1 + h) * ((N : ℝ) + 1) := by
      rw [hh]; field_simp; ring
    have hhN : h * ((N : ℝ) + 1) = 1 := by rw [hh]; field_simp
    show 1 ≤ (1 - Real.exp (-h)) * ((N : ℝ) + 2)
    rw [hN2]
    nlinarith [Real.exp_pos (-h), show (0 : ℝ) < (N : ℝ) + 1 by positivity]
  · set h := 1 / ((N : ℝ) + 1) with hh
    have h1 : 1 - h ≤ Real.exp (-h) := by linarith [Real.add_one_le_exp (-h)]
    have hN2 : (N : ℝ) + 2 = (1 + h) * ((N : ℝ) + 1) := by
      rw [hh]; field_simp; ring
    have hhN : h * ((N : ℝ) + 1) = 1 := by rw [hh]; field_simp
    show (1 - Real.exp (-h)) * ((N : ℝ) + 2) ≤ 1 + h
    rw [hN2]
    have hp : (0 : ℝ) ≤ (1 + h) * ((N : ℝ) + 1) := by positivity
    nlinarith [show (0 : ℝ) < h by positivity]

/-- The Tauberian direction: Abel convergence to a finite limit implies Cesàro convergence. -/
theorem bwReuse_tauberian_theorem_tt_cesaro (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) :
    Tendsto (cesaroMean u) atTop (𝓝 L) := by
  have hr := (abel_limit_r u hu0 L hL hlim).comp bwReuse_tauberian_theorem_ttA_tendsto
  have hI : ∫ x in (0 : ℝ)..1, r x = 1 := integral_r.1.trans integral_r.2
  rw [hI, ENNReal.ofReal_one, mul_one] at hr
  have hG : Tendsto (fun N : ℕ => (1 - ((bwReuse_tauberian_theorem_ttA N : ℝ≥0) : ℝ≥0∞)) * w u (N + 2)) atTop (𝓝 L) := by
    refine hr.congr fun N => ?_
    simp only [Function.comp]
    rw [bwReuse_tauberian_theorem_tt_sum]
  have hd : Tendsto (fun N : ℕ => ((1 - ((bwReuse_tauberian_theorem_ttA N : ℝ≥0) : ℝ≥0∞)) * ((N : ℝ≥0∞) + 2))⁻¹) atTop
      (𝓝 1) := by
    have := tendsto_inv_iff.mpr bwReuse_tauberian_theorem_tt_ratio
    rwa [inv_one] at this
  have hprod := ENNReal.Tendsto.mul hG (Or.inr ENNReal.one_ne_top) hd (Or.inr hL)
  rw [mul_one] at hprod
  rw [← tendsto_add_atTop_iff_nat 2]
  refine hprod.congr fun N => ?_
  have hα : ((bwReuse_tauberian_theorem_ttA N : ℝ≥0) : ℝ≥0∞) < 1 := by exact_mod_cast bwReuse_tauberian_theorem_ttA_lt_one N
  have h0 : (1 - ((bwReuse_tauberian_theorem_ttA N : ℝ≥0) : ℝ≥0∞)) ≠ 0 := (tsub_pos_of_lt hα).ne'
  have ht : (1 - ((bwReuse_tauberian_theorem_ttA N : ℝ≥0) : ℝ≥0∞)) ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  unfold cesaroMean
  rw [ENNReal.mul_inv (Or.inl h0) (Or.inl ht), div_eq_mul_inv]
  have hc : ((N + 2 : ℕ) : ℝ≥0∞) = (N : ℝ≥0∞) + 2 := by push_cast; ring
  rw [hc]
  calc (1 - ((bwReuse_tauberian_theorem_ttA N : ℝ≥0) : ℝ≥0∞)) * w u (N + 2) *
        ((1 - ((bwReuse_tauberian_theorem_ttA N : ℝ≥0) : ℝ≥0∞))⁻¹ * ((N : ℝ≥0∞) + 2)⁻¹)
      = ((1 - ((bwReuse_tauberian_theorem_ttA N : ℝ≥0) : ℝ≥0∞)) * (1 - ((bwReuse_tauberian_theorem_ttA N : ℝ≥0) : ℝ≥0∞))⁻¹) *
          (w u (N + 2) * ((N : ℝ≥0∞) + 2)⁻¹) := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel h0 ht, one_mul]

end SennottDP.Tauberian

open SennottDP.Tauberian in
theorem _root_.SennottDP.Tauberian.tauberian_theorem (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) :
    (liminf (cesaroMean u) atTop ≤ liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) ∧
      liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) ≤ limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) ∧
      limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) ≤ limsup (cesaroMean u) atTop) ∧
    List.TFAE
      [liminf (cesaroMean u) atTop = liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) ∧
          liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) = limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) ∧
          limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) = limsup (cesaroMean u) atTop ∧
          limsup (cesaroMean u) atTop ≠ ⊤,
        ∃ L : ℝ≥0∞, L ≠ ⊤ ∧ Tendsto (cesaroMean u) atTop (𝓝 L),
        ∃ L : ℝ≥0∞, L ≠ ⊤ ∧ Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)] := by
  have : (𝓝[<] (1 : ℝ≥0)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, zero_lt_one⟩
  have hab := abelian_inequalities u hu0
  obtain ⟨h1, h2, h3⟩ := id hab
  refine ⟨hab, ?_⟩
  tfae_have 1 → 2 := by
    rintro ⟨e1, e2, e3, hne⟩
    refine ⟨limsup (cesaroMean u) atTop, hne, ?_⟩
    exact tendsto_of_liminf_eq_limsup (e1.trans (e2.trans e3)) rfl
  tfae_have 2 → 3 := by
    rintro ⟨L, hL, ht⟩
    refine ⟨L, hL, ?_⟩
    have hli := ht.liminf_eq
    have hls := ht.limsup_eq
    have a1 : liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) = L :=
      le_antisymm (h2.trans (h3.trans hls.le)) (hli ▸ h1)
    have a2 : limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) = L :=
      le_antisymm (hls ▸ h3) (hli ▸ (h1.trans h2))
    exact tendsto_of_liminf_eq_limsup a1 a2
  tfae_have 3 → 1 := by
    rintro ⟨L, hL, ht⟩
    have hc := bwReuse_tauberian_theorem_tt_cesaro u hu0 L hL ht
    rw [hc.liminf_eq, hc.limsup_eq, ht.liminf_eq, ht.limsup_eq]
    exact ⟨rfl, rfl, rfl, hL⟩
  tfae_finish




namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Topology
open Classical Filter
noncomputable section
variable {S Act : Type*} [Countable S]

lemma bf_initial_cost_finite (M : MDC S Act) (θ : Policy M) (i : S) : expCost θ i 0 ≠ ⊤ := by
  rw [← bf_expectedCost,SennottDP.BlackwellFH.fa_initialCost]
  apply ENNReal.sum_ne_top.mpr
  intro a ha
  apply ENNReal.mul_ne_top
  · apply ne_top_of_le_ne_top ENNReal.one_ne_top
    change θ.prob [] i a ≤ 1
    rw [← θ.prob_sum [] i]
    exact Finset.single_le_sum (fun b _ => bot_le) ha
  · finiteness

lemma bf_coe_map_nhdsLT : (𝓝[<] (1 : ℝ≥0)).map NNReal.toReal = 𝓝[<] (1 : ℝ) := by
  rw [NNReal.isEmbedding_coe.map_nhdsWithin_eq,NNReal.image_coe_Iio]
  change 𝓝[Set.Ici 0 ∩ Set.Iio 1] (1 : ℝ) = 𝓝[Set.Iio 1] (1 : ℝ)
  exact nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds (by norm_num)))

lemma bf_abel_coe (M : MDC S Act) (θ : Policy M) (i : S) (α : ℝ≥0) :
    ENNReal.ofReal (1-(α : ℝ)) * discCost θ α i = SennottDP.Tauberian.abelMean (expCost θ i) α := by
  simp [SennottDP.Tauberian.abelMean,SennottDP.Tauberian.U,discCost,ENNReal.ofReal_sub _ α.coe_nonneg]

lemma bf_cesaro (M : MDC S Act) (θ : Policy M) (i : S) :
    (fun n => horizonCost θ n i / (n : ℝ≥0∞)) = SennottDP.Tauberian.cesaroMean (expCost θ i) := rfl

lemma bf_abel_result (M : MDC S Act) (θ : Policy M) (i : S) :
    let F : ℝ → ℝ≥0∞ := fun α => ENNReal.ofReal (1-α) * discCost θ α i
    avgCostLiminf θ i ≤ liminf F (𝓝[<] (1 : ℝ)) ∧
    liminf F (𝓝[<] (1 : ℝ)) ≤ limsup F (𝓝[<] (1 : ℝ)) ∧
    limsup F (𝓝[<] (1 : ℝ)) ≤ avgCost θ i ∧
    List.TFAE
      [avgCostLiminf θ i = liminf F (𝓝[<] (1 : ℝ)) ∧
         liminf F (𝓝[<] (1 : ℝ)) = limsup F (𝓝[<] (1 : ℝ)) ∧
         limsup F (𝓝[<] (1 : ℝ)) = avgCost θ i ∧ avgCost θ i < ⊤,
       avgCostLiminf θ i = avgCost θ i ∧ avgCost θ i < ⊤,
       ∃ L : ℝ≥0∞, L < ⊤ ∧ Tendsto F (𝓝[<] (1 : ℝ)) (𝓝 L)] ∧
    (avgCostLiminf θ i = avgCost θ i ∧ avgCost θ i < ⊤ →
      Tendsto (fun n : ℕ => horizonCost θ n i / (n : ℝ≥0∞)) atTop (𝓝 (avgCost θ i))) := by
  let F : ℝ → ℝ≥0∞ := fun α => ENNReal.ofReal (1-α) * discCost θ α i
  have hf : F ∘ NNReal.toReal = SennottDP.Tauberian.abelMean (expCost θ i) := by
    funext α
    exact bf_abel_coe M θ i α
  have hli : liminf (SennottDP.Tauberian.abelMean (expCost θ i)) (𝓝[<] (1 : ℝ≥0)) = liminf F (𝓝[<] (1 : ℝ)) := by
    rw [← hf,liminf_comp,bf_coe_map_nhdsLT]
  have hls : limsup (SennottDP.Tauberian.abelMean (expCost θ i)) (𝓝[<] (1 : ℝ≥0)) = limsup F (𝓝[<] (1 : ℝ)) := by
    rw [← hf,limsup_comp,bf_coe_map_nhdsLT]
  have hlim (L : ℝ≥0∞) : Tendsto (SennottDP.Tauberian.abelMean (expCost θ i)) (𝓝[<] (1 : ℝ≥0)) (𝓝 L) ↔ Tendsto F (𝓝[<] (1 : ℝ)) (𝓝 L) := by
    rw [← hf,← tendsto_map'_iff,bf_coe_map_nhdsLT]
  have ht := SennottDP.Tauberian.tauberian_theorem (expCost θ i) (bf_initial_cost_finite M θ i)
  have ha : avgCostLiminf θ i ≤ liminf F (𝓝[<] (1 : ℝ)) ∧
      liminf F (𝓝[<] (1 : ℝ)) ≤ limsup F (𝓝[<] (1 : ℝ)) ∧
      limsup F (𝓝[<] (1 : ℝ)) ≤ avgCost θ i := by
    simpa only [hli,hls,avgCostLiminf,avgCost,bf_cesaro] using ht.1
  have hc : avgCostLiminf θ i = avgCost θ i ∧ avgCost θ i < ⊤ →
      Tendsto (fun n : ℕ => horizonCost θ n i / (n : ℝ≥0∞)) atTop (𝓝 (avgCost θ i)) := by
    rintro ⟨he,hn⟩
    exact tendsto_of_liminf_eq_limsup he rfl
  refine ⟨ha.1,ha.2.1,ha.2.2,?_,hc⟩
  tfae_have 1 → 2 := by
    rintro ⟨h1,h2,h3,hn⟩
    exact ⟨h1.trans (h2.trans h3),hn⟩
  tfae_have 2 → 3 := by
    intro h
    have hct := hc h
    have hs : ∃ L : ℝ≥0∞, L ≠ ⊤ ∧ Tendsto (SennottDP.Tauberian.cesaroMean (expCost θ i)) atTop (𝓝 L) :=
      ⟨avgCost θ i,ne_top_of_lt h.2,hct⟩
    obtain ⟨L,hL,hT⟩ := (ht.2.out 1 2).mp hs
    exact ⟨L,lt_top_iff_ne_top.mpr hL,(hlim L).mp hT⟩
  tfae_have 3 → 1 := by
    rintro ⟨L,hL,hT⟩
    have hs : ∃ L : ℝ≥0∞, L ≠ ⊤ ∧ Tendsto (SennottDP.Tauberian.abelMean (expCost θ i)) (𝓝[<] (1 : ℝ≥0)) (𝓝 L) :=
      ⟨L,ne_top_of_lt hL,(hlim L).mpr hT⟩
    have h := (ht.2.out 2 0).mp hs
    simpa only [hli,hls,avgCostLiminf,avgCost,bf_cesaro,lt_top_iff_ne_top] using h
  tfae_finish

end
end SennottDP.AvgFinite

open SennottDP.AvgFinite

open scoped ENNReal NNReal Topology
open Filter

/-- Proposition 6.1.1 (Sennott, p. 98). For an MDC with countable state space, any policy `θ` and
initial state `i`,
`J*_θ(i) ≤ liminf_{α→1⁻} (1−α)V_{θ,α}(i) ≤ limsup_{α→1⁻} (1−α)V_{θ,α}(i) ≤ J_θ(i)` (6.1),
and the following are equivalent: (i) all the terms in (6.1) are equal and finite;
(ii) `J*_θ(i) = J_θ(i) < ∞`; (iii) `lim_{α→1⁻} (1−α)V_{θ,α}(i)` exists and is finite. Moreover
under (ii) the quantity in (2.15) is obtained as a limit. -/
theorem solution {S : Type*} {Act : Type*} [Countable S] (M : MDC S Act)
    (θ : Policy M) (i : S) :
    let F : ℝ → ℝ≥0∞ := fun α => ENNReal.ofReal (1 - α) * discCost θ α i
    avgCostLiminf θ i ≤ liminf F (𝓝[<] (1 : ℝ)) ∧
    liminf F (𝓝[<] (1 : ℝ)) ≤ limsup F (𝓝[<] (1 : ℝ)) ∧
    limsup F (𝓝[<] (1 : ℝ)) ≤ avgCost θ i ∧
    List.TFAE
      [ avgCostLiminf θ i = liminf F (𝓝[<] (1 : ℝ)) ∧
          liminf F (𝓝[<] (1 : ℝ)) = limsup F (𝓝[<] (1 : ℝ)) ∧
          limsup F (𝓝[<] (1 : ℝ)) = avgCost θ i ∧ avgCost θ i < ⊤,
        avgCostLiminf θ i = avgCost θ i ∧ avgCost θ i < ⊤,
        ∃ L : ℝ≥0∞, L < ⊤ ∧ Tendsto F (𝓝[<] (1 : ℝ)) (𝓝 L) ] ∧
    (avgCostLiminf θ i = avgCost θ i ∧ avgCost θ i < ⊤ →
      Tendsto (fun n : ℕ => horizonCost θ n i / (n : ℝ≥0∞)) atTop (𝓝 (avgCost θ i))) := by
  exact bf_abel_result M θ i

#print axioms solution

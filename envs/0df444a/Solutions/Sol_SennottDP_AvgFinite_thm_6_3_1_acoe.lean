-- Prove2me | solution 1 for SennottDP.AvgFinite.thm_6_3_1_acoe
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T03:07:16.006032+00:00
-- url     : https://prove2.me/submissions/58dc23f1-99f0-4be7-b5cb-7a438ef1c76b

import Definitions.Def_SennottDP_AvgFinite_ACOE
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


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S Act : Type*} [Fintype S]

lemma bf_cost_bound (M : MDC S Act) : ∃ B : ℝ≥0, ∀ i, ∀ a ∈ M.A i, M.C i a ≤ B := by
  refine ⟨∑ i, (M.A i).sup (M.C i),fun i a ha => ?_⟩
  have hs : (M.A i).sup (M.C i) ≤ ∑ j, (M.A j).sup (M.C j) := by
    exact Finset.single_le_sum (f := fun j : S => (M.A j).sup (M.C j)) (fun j _ => by positivity) (Finset.mem_univ i)
  exact (Finset.le_sup ha).trans hs

lemma bf_P_le_one (M : MDC S Act) (i : S) (a : Act) (j : S) : M.P i a j ≤ 1 := by
  rw [← M.P_sum i a]
  exact ENNReal.le_tsum j

lemma bf_disc_finite (M : MDC S Act) (θ : Policy M) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) (i : S) :
    discCost θ α i ≠ ⊤ := by
  obtain ⟨B,hB⟩ := bf_cost_bound M
  have hb : discCost θ α i ≤ (B : ℝ≥0∞) * ENNReal.ofReal (1 / (1-α)) := by
    unfold discCost
    calc
      _ ≤ ∑' t : ℕ, (B : ℝ≥0∞) * ENNReal.ofReal α ^ t := by
        exact ENNReal.tsum_le_tsum (fun t => by
          rw [mul_comm (B : ℝ≥0∞)]
          exact mul_le_mul_right (C455.c455_expCost_le B hB θ i t) _)
      _ = _ := by
        rw [ENNReal.tsum_mul_left]
        congr 1
        simp_rw [← ENNReal.ofReal_pow hα.1.le]
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => pow_nonneg hα.1.le t)
          (summable_geometric_of_lt_one hα.1.le hα.2),tsum_geometric_of_lt_one hα.1.le hα.2]
        simp [one_div]
  exact ne_top_of_le_ne_top (by finiteness) hb

lemma bf_disc_rec (M : MDC S Act) (e : StationaryPolicy M) (α : ℝ) (i : S) :
    discCost e.toPolicy α i = (M.C i (e.f i) : ℝ≥0∞) +
      ENNReal.ofReal α * ∑' j, M.P i (e.f i) j * discCost e.toPolicy α j := by
  unfold discCost
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [pow_zero,one_mul,bf_expCost_zero,bf_expCost_succ,pow_succ]
  congr 1
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro j
  apply tsum_congr
  intro t
  ring

def bf_P (M : MDC S Act) (e : StationaryPolicy M) : Matrix S S ℝ := fun i j => (M.P i (e.f i) j).toReal

def bf_c (M : MDC S Act) (e : StationaryPolicy M) : S → ℝ := fun i => M.C i (e.f i)

def bf_v (M : MDC S Act) (e : StationaryPolicy M) (α : ℝ) : S → ℝ :=
  fun i => (discCost e.toPolicy α i).toReal

def bf_A (M : MDC S Act) (e : StationaryPolicy M) (α : ℝ) : Matrix S S ℝ := 1 - α • bf_P M e

lemma bf_P_nonneg (M : MDC S Act) (e : StationaryPolicy M) (i j : S) : 0 ≤ bf_P M e i j :=
  ENNReal.toReal_nonneg

lemma bf_P_sum (M : MDC S Act) (e : StationaryPolicy M) (i : S) : ∑ j, bf_P M e i j = 1 := by
  have h := M.P_sum i (e.f i)
  rw [tsum_fintype] at h
  have ht := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_sum (fun j _ => ne_top_of_le_ne_top ENNReal.one_ne_top (bf_P_le_one M i (e.f i) j))] at ht
  simpa [bf_P] using ht

lemma bf_P_norm (M : MDC S Act) (e : StationaryPolicy M) (v : S → ℝ) :
    ‖(bf_P M e).mulVec v‖ ≤ ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
  intro i
  calc
    ‖(bf_P M e).mulVec v i‖ ≤ ∑ j, ‖bf_P M e i j * v j‖ := norm_sum_le _ _
    _ ≤ ∑ j, bf_P M e i j * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (bf_P_nonneg M e i j)]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (bf_P_nonneg M e i j)
    _ = ‖v‖ := by rw [← Finset.sum_mul,bf_P_sum,one_mul]

lemma bf_A_det_ne (M : MDC S Act) (e : StationaryPolicy M) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    (bf_A M e α).det ≠ 0 := by
  have hi : Function.Injective (bf_A M e α).mulVec := by
    intro u v h
    have hd : (bf_A M e α).mulVec (u-v) = 0 := by
      rw [Matrix.mulVec_sub,h,sub_self]
    have he : u-v = α • (bf_P M e).mulVec (u-v) := by
      rw [bf_A,Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec] at hd
      exact sub_eq_zero.mp hd
    have hn : ‖u-v‖ ≤ α * ‖u-v‖ := by
      calc
        ‖u-v‖ = α * ‖(bf_P M e).mulVec (u-v)‖ := by
          conv_lhs => rw [he]
          rw [norm_smul,Real.norm_eq_abs,abs_of_pos hα.1]
        _ ≤ α * ‖u-v‖ := mul_le_mul_of_nonneg_left (bf_P_norm M e _) hα.1.le
    have hz : ‖u-v‖ = 0 := by nlinarith [norm_nonneg (u-v),hα.2]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hi)).ne_zero

lemma bf_v_equation (M : MDC S Act) (e : StationaryPolicy M) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    (bf_A M e α).mulVec (bf_v M e α) = bf_c M e := by
  rw [bf_A,Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec]
  funext i
  have h := congrArg ENNReal.toReal (bf_disc_rec M e α i)
  rw [ENNReal.toReal_add (by finiteness) (by
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    rw [tsum_fintype]
    exact ENNReal.sum_ne_top.mpr (fun j _ => ENNReal.mul_ne_top
      (ne_top_of_le_ne_top ENNReal.one_ne_top (bf_P_le_one M i (e.f i) j)) (bf_disc_finite M e.toPolicy hα j))),
    ENNReal.toReal_mul,ENNReal.toReal_ofReal hα.1.le,tsum_fintype,
    ENNReal.toReal_sum (fun j _ => ENNReal.mul_ne_top
      (ne_top_of_le_ne_top ENNReal.one_ne_top (bf_P_le_one M i (e.f i) j)) (bf_disc_finite M e.toPolicy hα j))] at h
  simp only [ENNReal.toReal_mul,ENNReal.coe_toReal] at h
  change (discCost e.toPolicy α i).toReal - α * (∑ j, (M.P i (e.f i) j).toReal * (discCost e.toPolicy α j).toReal) = (M.C i (e.f i) : ℝ)
  linarith

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S Act : Type*} [Fintype S]

def bf_polyA (M : MDC S Act) (e : StationaryPolicy M) : Matrix S S (Polynomial ℝ) :=
  fun i j => Polynomial.C (if i = j then 1 else 0) - Polynomial.X * Polynomial.C (bf_P M e i j)

lemma bf_polyA_eval (M : MDC S Act) (e : StationaryPolicy M) (α : ℝ) :
    (bf_polyA M e).map (Polynomial.evalRingHom α) = bf_A M e α := by
  ext i j
  change (Polynomial.C (if i = j then 1 else 0) - Polynomial.X * Polynomial.C (bf_P M e i j)).eval α =
    (if i = j then 1 else 0) - α * bf_P M e i j
  rw [Polynomial.eval_sub,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C]

lemma bf_polyA_det_eval (M : MDC S Act) (e : StationaryPolicy M) (α : ℝ) :
    (bf_polyA M e).det.eval α = (bf_A M e α).det := by
  change (Polynomial.evalRingHom α) _ = _
  rw [RingHom.map_det]
  change ((bf_polyA M e).map (Polynomial.evalRingHom α)).det = _
  rw [bf_polyA_eval]

lemma bf_polyA_numerator_eval (M : MDC S Act) (e : StationaryPolicy M) (i : S) (α : ℝ) :
    ((bf_polyA M e).updateCol i (fun j => Polynomial.C (bf_c M e j))).det.eval α =
      ((bf_A M e α).updateCol i (bf_c M e)).det := by
  change (Polynomial.evalRingHom α) _ = _
  rw [RingHom.map_det]
  congr 1
  ext j k
  by_cases hk : k = i
  · subst k
    simp [Matrix.map,Matrix.updateCol]
  · simp [Matrix.map,Matrix.updateCol,hk]
    exact congrFun (congrFun (bf_polyA_eval M e α) j) k

lemma bf_rational_data (M : MDC S Act) (e : StationaryPolicy M) (i : S) :
    ∃ p q : Polynomial ℝ, ∀ α ∈ Set.Ioo (0 : ℝ) 1,
      q.eval α ≠ 0 ∧ bf_v M e α i = p.eval α / q.eval α := by
  refine ⟨((bf_polyA M e).updateCol i (fun j => Polynomial.C (bf_c M e j))).det,
    (bf_polyA M e).det,fun α hα => ?_⟩
  rw [bf_polyA_det_eval,bf_polyA_numerator_eval]
  refine ⟨bf_A_det_ne M e hα,?_⟩
  apply (eq_div_iff (bf_A_det_ne M e hα)).mpr
  have h := Matrix.det_smul_inv_mulVec_eq_cramer (bf_A M e α) (bf_c M e)
    (isUnit_iff_ne_zero.mpr (bf_A_det_ne M e hα))
  have hv : (bf_A M e α)⁻¹.mulVec (bf_c M e) = bf_v M e α := by
    rw [← bf_v_equation M e hα,Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (bf_A_det_ne M e hα)),Matrix.one_mulVec]
  rw [hv] at h
  have hi := congrFun h i
  simpa [Pi.smul_apply,smul_eq_mul,Matrix.cramer_apply,mul_comm] using hi

lemma bf_rational_result (M : MDC S Act) (e : StationaryPolicy M) (i : S) :
    (∀ α ∈ Set.Ioo (0 : ℝ) 1, discCost e.toPolicy α i ≠ ⊤) ∧
    ContinuousOn (fun α : ℝ => (discCost e.toPolicy α i).toReal) (Set.Ioo 0 1) ∧
    ∃ p q : Polynomial ℝ, ∀ α ∈ Set.Ioo (0 : ℝ) 1,
      q.eval α ≠ 0 ∧ (discCost e.toPolicy α i).toReal = p.eval α / q.eval α := by
  obtain ⟨p,q,h⟩ := bf_rational_data M e i
  refine ⟨fun α hα => bf_disc_finite M e.toPolicy hα i,?_,p,q,h⟩
  apply ContinuousOn.congr (f := fun α => p.eval α / q.eval α)
  · exact p.continuous.continuousOn.div q.continuous.continuousOn (fun α hα => (h α hα).1)
  · intro α hα
    exact (h α hα).2

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open Classical Filter Topology
noncomputable section

lemma bf_meromorphic_limit (p q : Polynomial ℝ) (B : ℝ)
    (hb : ∀ᶠ α : ℝ in 𝓝[<] 1, ‖p.eval α / q.eval α‖ ≤ B) :
    ∃ L : ℝ, Tendsto (fun α : ℝ => p.eval α / q.eval α) (𝓝[<] 1) (𝓝 L) := by
  have hp : AnalyticAt ℝ (fun α : ℝ => p.eval α) 1 := (AnalyticOnNhd.eval_polynomial p) 1 (Set.mem_univ 1)
  have hq : AnalyticAt ℝ (fun α : ℝ => q.eval α) 1 := (AnalyticOnNhd.eval_polynomial q) 1 (Set.mem_univ 1)
  have hm := hp.meromorphicAt.div hq.meromorphicAt
  have hle : 𝓝[<] (1 : ℝ) ≤ 𝓝[≠] (1 : ℝ) :=
    nhdsWithin_mono _ (fun α hα => ne_of_lt hα)
  have ho : 0 ≤ meromorphicOrderAt (fun α : ℝ => p.eval α / q.eval α) 1 := by
    by_contra h
    have ht := (tendsto_cobounded_of_meromorphicOrderAt_neg (lt_of_not_ge h)).mono_left hle
    have hn := tendsto_norm_atTop_iff_cobounded.mpr ht
    obtain ⟨α,hbα,hα⟩ := (hb.and (hn.eventually (eventually_gt_atTop (B+1)))).exists
    linarith
  obtain ⟨L,hL⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hm ho
  exact ⟨L,hL.mono_left hle⟩

lemma bf_polynomial_sign_near (p : Polynomial ℝ) :
    (∀ α : ℝ, p.eval α = 0) ∨
    (∀ᶠ α : ℝ in 𝓝[<] 1, 0 < p.eval α) ∨
    (∀ᶠ α : ℝ in 𝓝[<] 1, p.eval α < 0) := by
  by_cases hp : p = 0
  · subst p
    exact Or.inl (by simp)
  right
  obtain ⟨q,hpq,hq⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp 1
  have hq1 : q.eval 1 ≠ 0 := by
    intro h
    exact hq (Polynomial.dvd_iff_isRoot.mpr h)
  have hleft : ∀ᶠ α : ℝ in 𝓝[<] 1, α < 1 := self_mem_nhdsWithin
  rcases lt_or_gt_of_ne hq1 with hqneg | hqpos
  · have hn : ∀ᶠ α : ℝ in 𝓝[<] 1, q.eval α < 0 :=
      (q.continuous.continuousAt.eventually (Iio_mem_nhds hqneg)).filter_mono nhdsWithin_le_nhds
    by_cases he : Even (p.rootMultiplicity 1)
    · right
      filter_upwards [hn,hleft] with α hα hα1
      rw [hpq,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
      exact mul_neg_of_pos_of_neg (he.pow_pos (ne_of_lt (sub_lt_zero.mpr hα1))) hα
    · left
      filter_upwards [hn,hleft] with α hα hα1
      rw [hpq,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
      exact mul_pos_of_neg_of_neg ((Nat.not_even_iff_odd.mp he).pow_neg_iff.mpr (sub_lt_zero.mpr hα1)) hα
  · have hn : ∀ᶠ α : ℝ in 𝓝[<] 1, 0 < q.eval α :=
      (q.continuous.continuousAt.eventually (Ioi_mem_nhds hqpos)).filter_mono nhdsWithin_le_nhds
    by_cases he : Even (p.rootMultiplicity 1)
    · left
      filter_upwards [hn,hleft] with α hα hα1
      rw [hpq,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
      exact mul_pos (he.pow_pos (ne_of_lt (sub_lt_zero.mpr hα1))) hα
    · right
      filter_upwards [hn,hleft] with α hα hα1
      rw [hpq,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
      exact mul_neg_of_neg_of_pos ((Nat.not_even_iff_odd.mp he).pow_neg_iff.mpr (sub_lt_zero.mpr hα1)) hα

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


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Topology
open Classical Filter
noncomputable section
variable {S Act : Type*} [Fintype S]

lemma bf_disc_bound (M : MDC S Act) (B : ℝ≥0) (hB : ∀ i, ∀ a ∈ M.A i, M.C i a ≤ B)
    (θ : Policy M) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) (i : S) :
    (discCost θ α i).toReal ≤ (B : ℝ) / (1-α) := by
  have hb : discCost θ α i ≤ (B : ℝ≥0∞) * ENNReal.ofReal (1 / (1-α)) := by
    unfold discCost
    calc
      _ ≤ ∑' t : ℕ, (B : ℝ≥0∞) * ENNReal.ofReal α ^ t := by
        exact ENNReal.tsum_le_tsum (fun t => by
          rw [mul_comm (B : ℝ≥0∞)]
          exact mul_le_mul_right (C455.c455_expCost_le B hB θ i t) _)
      _ = _ := by
        rw [ENNReal.tsum_mul_left]
        congr 1
        simp_rw [← ENNReal.ofReal_pow hα.1.le]
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => pow_nonneg hα.1.le t)
          (summable_geometric_of_lt_one hα.1.le hα.2),tsum_geometric_of_lt_one hα.1.le hα.2]
        simp [one_div]
  have h := (ENNReal.toReal_le_toReal (bf_disc_finite M θ hα i) (by finiteness)).mpr hb
  rw [ENNReal.toReal_mul,ENNReal.coe_toReal,ENNReal.toReal_ofReal (one_div_pos.mpr (sub_pos.mpr hα.2)).le] at h
  simpa [div_eq_mul_inv] using h

lemma bf_normalized_bound (M : MDC S Act) (B : ℝ≥0) (hB : ∀ i, ∀ a ∈ M.A i, M.C i a ≤ B)
    (e : StationaryPolicy M) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) (i : S) :
    ‖(1-α)*bf_v M e α i‖ ≤ B := by
  have hv : 0 ≤ bf_v M e α i := ENNReal.toReal_nonneg
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hα.2.le) hv)]
  calc
    _ ≤ (1-α) * ((B : ℝ)/(1-α)) := mul_le_mul_of_nonneg_left (bf_disc_bound M B hB e.toPolicy hα i) (sub_nonneg.mpr hα.2.le)
    _ = B := by field_simp [ne_of_gt (sub_pos.mpr hα.2)]

lemma bf_stationary_abel_exists (M : MDC S Act) (e : StationaryPolicy M) (i : S) :
    ∃ L : ℝ≥0∞, L < ⊤ ∧ Tendsto (fun α : ℝ => ENNReal.ofReal (1-α) * discCost e.toPolicy α i)
      (𝓝[<] 1) (𝓝 L) := by
  obtain ⟨p,q,hpq⟩ := bf_rational_data M e i
  obtain ⟨B,hB⟩ := bf_cost_bound M
  let p' := (1 - Polynomial.X) * p
  have he (α : ℝ) (hα : α ∈ Set.Ioo 0 1) : p'.eval α / q.eval α = (1-α)*bf_v M e α i := by
    rw [(hpq α hα).2]
    simp [p',Polynomial.eval_mul,mul_div_assoc]
  have hb : ∀ᶠ α : ℝ in 𝓝[<] 1, ‖p'.eval α / q.eval α‖ ≤ B := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with α hα
    rw [he α hα]
    exact bf_normalized_bound M B hB e hα i
  obtain ⟨L,hL⟩ := bf_meromorphic_limit p' q B hb
  refine ⟨ENNReal.ofReal L,ENNReal.ofReal_lt_top,?_⟩
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hL
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with α hα
  change ENNReal.ofReal (p'.eval α / q.eval α) = _
  rw [he α hα]
  change ENNReal.ofReal ((1-α)*(discCost e.toPolicy α i).toReal) = _
  rw [ENNReal.ofReal_mul (sub_nonneg.mpr hα.2.le),ENNReal.ofReal_toReal (bf_disc_finite M e.toPolicy hα i)]

lemma bf_stationary_limits_result (M : MDC S Act) (e : StationaryPolicy M) (i : S) :
    Tendsto (fun α : ℝ => ENNReal.ofReal (1-α) * discCost e.toPolicy α i) (𝓝[<] 1)
      (𝓝 (avgCost e.toPolicy i)) ∧
    Tendsto (fun n : ℕ => horizonCost e.toPolicy n i / (n : ℝ≥0∞)) atTop
      (𝓝 (avgCost e.toPolicy i)) := by
  have h := bf_abel_result M e.toPolicy i
  have hs := bf_stationary_abel_exists M e i
  have ha := (h.2.2.2.1.out 2 0).mp hs
  have hi : avgCostLiminf e.toPolicy i = avgCost e.toPolicy i ∧ avgCost e.toPolicy i < ⊤ :=
    (h.2.2.2.1.out 0 1).mp ha
  refine ⟨?_,h.2.2.2.2 hi⟩
  exact tendsto_of_liminf_eq_limsup (ha.2.1.trans ha.2.2.1) ha.2.2.1

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S : Type*} [Fintype S]

lemma bc_nStep_pow (Q : S → S → ℝ≥0∞) (n : ℕ) : Matrix.of (nStep Q n) = (Matrix.of Q)^n := by
  induction n with
  | zero => ext i j; simp [nStep,Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ,← ih]
    rfl

lemma bc_nStep_backward (Q : S → S → ℝ≥0∞) (n : ℕ) (i j : S) :
    nStep Q (n+1) i j = ∑ k, Q i k * nStep Q n k j := by
  change Matrix.of (nStep Q (n+1)) i j = _
  rw [bc_nStep_pow,pow_succ',← bc_nStep_pow]
  rfl

lemma bc_nStep_sum (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (n : ℕ) (i : S) :
    ∑ j, nStep Q n i j = 1 := by
  induction n generalizing i with
  | zero => simp [nStep]
  | succ n ih =>
    simp only [nStep,Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum,hQ,mul_one]
    exact ih i

lemma bc_nStep_le_one (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (n : ℕ) (i j : S) :
    nStep Q n i j ≤ 1 := by
  rw [← bc_nStep_sum Q hQ n i]
  exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ j)

def bc_model (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (C : S → ℝ≥0) : MDC S Unit where
  A _ := {()}
  A_nonempty _ := Finset.singleton_nonempty _
  C i _ := C i
  P i _ j := Q i j
  P_sum i _ := by rw [tsum_fintype]; exact hQ i

def bc_policy (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (C : S → ℝ≥0) :
    StationaryPolicy (bc_model Q hQ C) where
  f _ := ()
  mem _ := Finset.mem_singleton_self _

lemma bc_expCost_indicator (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S) (n : ℕ) (i : S) :
    expCost (bc_policy Q hQ (fun j => if j = z then 1 else 0)).toPolicy i n = nStep Q n i z := by
  induction n generalizing i with
  | zero => rw [bf_expCost_zero]; by_cases hi : i = z <;> simp [bc_model,bc_policy,nStep,hi]
  | succ n ih =>
    rw [bf_expCost_succ,tsum_fintype,bc_nStep_backward]
    apply Finset.sum_congr rfl
    intro j _
    rw [ih]
    rfl

lemma bc_firstPass_le_one (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1)
    (G : Set S) (n : ℕ) (i : S) : firstPassage Q G n i ≤ 1 := by
  induction n generalizing i with
  | zero => simp [firstPassage]
  | succ n ih =>
    simp only [firstPassage]
    split_ifs with hn
    · rw [← hQ i]
      apply Finset.sum_le_sum
      intro k _
      split_ifs <;> simp
    · rw [← hQ i]
      apply Finset.sum_le_sum
      intro k _
      split_ifs with hk
      · exact bot_le
      · exact (mul_le_mul_right (ih k) (Q i k)).trans_eq (mul_one _)

def bc_green (Q : S → S → ℝ≥0∞) (α : ℝ) (i j : S) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal α ^ n * nStep Q n i j

def bc_projection (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (i j : S) : ℝ≥0∞ :=
  avgCost (bc_policy Q hQ (fun k => if k = j then 1 else 0)).toPolicy i

lemma bc_green_eq (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (α : ℝ) (i j : S) :
    bc_green Q α i j = discCost (bc_policy Q hQ (fun k => if k = j then 1 else 0)).toPolicy α i := by
  unfold bc_green discCost
  simp_rw [bc_expCost_indicator]

lemma bc_green_limit (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (i j : S) :
    Tendsto (fun α : ℝ => ENNReal.ofReal (1-α) * bc_green Q α i j) (𝓝[<] 1)
      (𝓝 (bc_projection Q hQ i j)) := by
  simp_rw [bc_green_eq Q hQ]
  exact (bf_stationary_limits_result (bc_model Q hQ _) (bc_policy Q hQ _) i).1

lemma bc_cesaro_limit (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (i j : S) :
    Tendsto (fun n : ℕ => (∑ t ∈ Finset.range n, nStep Q t i j) / (n : ℝ≥0∞)) atTop
      (𝓝 (bc_projection Q hQ i j)) := by
  have h := (bf_stationary_limits_result (bc_model Q hQ (fun k => if k = j then 1 else 0))
    (bc_policy Q hQ _) i).2
  simpa only [horizonCost,bc_expCost_indicator,bc_projection] using h

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S : Type*} [Fintype S]

lemma bc_substoch_norm (R : Matrix S S ℝ) (hR : ∀ i j, 0 ≤ R i j)
    (hS : ∀ i, ∑ j, R i j ≤ 1) (v : S → ℝ) : ‖R.mulVec v‖ ≤ ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
  intro i
  calc
    ‖R.mulVec v i‖ ≤ ∑ j, ‖R i j * v j‖ := norm_sum_le _ _
    _ ≤ ∑ j, R i j * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hR i j)]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (hR i j)
    _ = (∑ j, R i j) * ‖v‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ ‖v‖ := by simpa using mul_le_mul_of_nonneg_right (hS i) (norm_nonneg v)

lemma bc_substoch_unique (R : Matrix S S ℝ) (hR : ∀ i j, 0 ≤ R i j)
    (hS : ∀ i, ∑ j, R i j ≤ 1) (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (c f g : S → ℝ) (hf : f = c + α • R.mulVec f) (hg : g = c + α • R.mulVec g) : f = g := by
  have hd : f-g = α • R.mulVec (f-g) := by
    rw [Matrix.mulVec_sub,smul_sub]
    calc
      f-g = (c + α • R.mulVec f) - (c + α • R.mulVec g) := congrArg₂ (·-·) hf hg
      _ = _ := by abel
  have hn : ‖f-g‖ ≤ α * ‖f-g‖ := by
    calc
      ‖f-g‖ = α * ‖R.mulVec (f-g)‖ := by
        conv_lhs => rw [hd]
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos hα.1]
      _ ≤ α * ‖f-g‖ := mul_le_mul_of_nonneg_left (bc_substoch_norm R hR hS _) hα.1.le
  have hz : ‖f-g‖ = 0 := by nlinarith [norm_nonneg (f-g),hα.2]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

lemma bc_Q_real_sum (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (i : S) :
    ∑ j, (Q i j).toReal = 1 := by
  simpa [bf_P,bc_model,bc_policy] using bf_P_sum (bc_model Q hQ (fun _ => 0)) (bc_policy Q hQ _) i

lemma bc_Q_ne_top (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (i j : S) : Q i j ≠ ⊤ := by
  apply ne_top_of_le_ne_top ENNReal.one_ne_top
  rw [← hQ i]
  exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ j)

def bc_kill (Q : S → S → ℝ≥0∞) (z : S) : Matrix S S ℝ :=
  Matrix.of fun i j => if j = z then 0 else (Q i j).toReal

lemma bc_kill_nonneg (Q : S → S → ℝ≥0∞) (z : S) (i j : S) : 0 ≤ bc_kill Q z i j := by
  simp only [bc_kill,Matrix.of_apply]
  split_ifs <;> positivity

lemma bc_kill_sum (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z i : S) :
    ∑ j, bc_kill Q z i j ≤ 1 := by
  rw [← bc_Q_real_sum Q hQ i]
  apply Finset.sum_le_sum
  intro j _
  simp only [bc_kill,Matrix.of_apply]
  split_ifs
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

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


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal
open Classical Filter Topology
open SennottDP.BlackwellFH
noncomputable section

def bc_series (u : ℕ → ℝ≥0∞) (α : ℝ) : ℝ≥0∞ := ∑' t : ℕ, ENNReal.ofReal α ^ t * u t

lemma bc_series_mono (u : ℕ → ℝ≥0∞) : Monotone (bc_series u) := by
  intro α β h
  exact ENNReal.tsum_le_tsum (fun t => by gcongr)

lemma bc_series_left_limit (u : ℕ → ℝ≥0∞) :
    Tendsto (bc_series u) (𝓝[<] (1 : ℝ)) (𝓝 (∑' t, u t)) := by
  obtain ⟨a,ha,hamem,hat⟩ := exists_seq_strictMono_tendsto' (show (0 : ℝ≥0) < 1 from zero_lt_one)
  have hpow (t : ℕ) : (⨆ n, (a n : ℝ≥0∞)^t) = 1 := by
    have ht := ENNReal.Tendsto.pow (n := t) (ENNReal.continuous_coe.continuousAt.tendsto.comp hat)
    simp only [ENNReal.coe_one,one_pow] at ht
    exact iSup_eq_of_tendsto (fun r s hrs => pow_le_pow_left₀ bot_le (ENNReal.coe_le_coe.mpr (ha.monotone hrs)) _) ht
  have hs : (⨆ n, bc_series u (a n)) = ∑' t, u t := by
    unfold bc_series
    simp only [ENNReal.ofReal_coe_nnreal]
    rw [← fa_tsum_iSup (fun n t => (a n : ℝ≥0∞)^t * u t)
      (fun t r s hrs => mul_le_mul' (pow_le_pow_left₀ bot_le (ENNReal.coe_le_coe.mpr (ha.monotone hrs)) t) le_rfl)]
    simp_rw [← ENNReal.iSup_mul,hpow,one_mul]
  have he : sSup (bc_series u '' Set.Iio (1 : ℝ)) = ∑' t, u t := by
    apply le_antisymm
    · apply sSup_le
      rintro v ⟨α,hα,rfl⟩
      unfold bc_series
      apply ENNReal.tsum_le_tsum
      intro t
      have hα1 : ENNReal.ofReal α ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal hα.le
      have hp : ENNReal.ofReal α ^ t ≤ 1 := by
        simpa using pow_le_pow_left₀ (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal α from bot_le) hα1 t
      exact (mul_le_mul' hp (le_refl (u t))).trans_eq (one_mul _)

    · rw [← hs]
      apply iSup_le
      intro n
      exact le_sSup ⟨(a n : ℝ),(hamem n).2,rfl⟩
  have ht := (bc_series_mono u).tendsto_nhdsLT (1 : ℝ)
  rwa [he] at ht

lemma bc_series_finite (u : ℕ → ℝ≥0∞) (hu : ∀ t, u t ≤ 1) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    bc_series u α ≠ ⊤ := by
  have hle : bc_series u α ≤ ENNReal.ofReal (1/(1-α)) := by
    unfold bc_series
    calc
      _ ≤ ∑' t : ℕ, ENNReal.ofReal α ^ t := ENNReal.tsum_le_tsum (fun t => by
        simpa using mul_le_mul_right (hu t) (ENNReal.ofReal α ^ t))
      _ = _ := by
        simp_rw [← ENNReal.ofReal_pow hα.1.le]
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => pow_nonneg hα.1.le t)
          (summable_geometric_of_lt_one hα.1.le hα.2),tsum_geometric_of_lt_one hα.1.le hα.2]
        simp [one_div]
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S : Type*} [Fintype S]

def bc_hitGen (Q : S → S → ℝ≥0∞) (z : S) (α : ℝ) (i : S) : ℝ≥0∞ :=
  bc_series (fun t => firstPassage Q {z} t i) α

lemma bc_firstPass_step (Q : S → S → ℝ≥0∞) (z : S) (n : ℕ) (i : S) :
    firstPassage Q {z} (n+1) i = (if n = 0 then Q i z else 0) +
      ∑ k, if k = z then 0 else Q i k * firstPassage Q {z} n k := by
  cases n with
  | zero => simp [firstPassage]
  | succ n => simp [firstPassage]

lemma bc_hitGen_rec (Q : S → S → ℝ≥0∞) (z : S) (α : ℝ) (i : S) :
    bc_hitGen Q z α i = ENNReal.ofReal α * Q i z +
      ENNReal.ofReal α * ∑ k, if k = z then 0 else Q i k * bc_hitGen Q z α k := by
  unfold bc_hitGen bc_series
  have hzero : firstPassage Q {z} 0 i = 0 := rfl
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [hzero,mul_zero,zero_add]
  simp_rw [bc_firstPass_step,pow_succ,mul_add,ENNReal.tsum_add]
  have hfirst : (∑' n : ℕ, ENNReal.ofReal α ^ n * ENNReal.ofReal α * (if n=0 then Q i z else 0)) = ENNReal.ofReal α * Q i z := by
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      simp [hn]
  rw [hfirst]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k = z
  · simp [hk]
  · simp only [hk,if_false]
    simp_rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro n
    ring

lemma bc_hitGen_finite (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 1) (i : S) : bc_hitGen Q z α i ≠ ⊤ :=
  bc_series_finite _ (fun t => bc_firstPass_le_one Q hQ {z} t i) hα

lemma bc_hitGen_limit (Q : S → S → ℝ≥0∞) (z i : S) :
    Tendsto (fun α : ℝ => bc_hitGen Q z α i) (𝓝[<] 1) (𝓝 (reachProb Q {z} i)) :=
  bc_series_left_limit _

lemma bc_hitGen_real_rec (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    (fun i => (bc_hitGen Q z α i).toReal) =
      α • (fun i => (Q i z).toReal) + α • (bc_kill Q z).mulVec (fun i => (bc_hitGen Q z α i).toReal) := by
  funext i
  have hv : ∀ k, (if k = z then 0 else Q i k * bc_hitGen Q z α k) ≠ ⊤ := by
    intro k
    split_ifs
    · finiteness
    · exact ENNReal.mul_ne_top (bc_Q_ne_top Q hQ i k) (bc_hitGen_finite Q hQ z hα k)
  have h := congrArg ENNReal.toReal (bc_hitGen_rec Q z α i)
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (bc_Q_ne_top Q hQ i z))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.sum_ne_top.mpr (fun k _ => hv k))),ENNReal.toReal_mul,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal hα.1.le,ENNReal.toReal_sum (fun k _ => hv k)] at h
  change (bc_hitGen Q z α i).toReal = α * (Q i z).toReal +
    α * ∑ k, bc_kill Q z i k * (bc_hitGen Q z α k).toReal
  rw [h]
  congr 2
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k = z <;> simp [hk,bc_kill,ENNReal.toReal_mul]

lemma bc_green_finite (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 1) (i j : S) : bc_green Q α i j ≠ ⊤ := by
  rw [bc_green_eq Q hQ]
  exact bf_disc_finite _ _ hα i

lemma bc_green_rec (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S) (α : ℝ) (i : S) :
    bc_green Q α i z = (if i=z then 1 else 0) +
      ENNReal.ofReal α * ∑ k, Q i k * bc_green Q α k z := by
  simp_rw [bc_green_eq Q hQ]
  rw [bf_disc_rec,tsum_fintype]
  by_cases hi : i=z <;> simp [bc_model,bc_policy,hi]

lemma bc_green_diagonal_ge_one (Q : S → S → ℝ≥0∞) (z : S) (α : ℝ) : 1 ≤ bc_green Q α z z := by
  have h := ENNReal.le_tsum 0 (f := fun n => ENNReal.ofReal α ^ n * nStep Q n z z)
  simpa [nStep,bc_green] using h

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S : Type*} [Fintype S]

lemma bc_mask_identity (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S) (v : S → ℝ) :
    (bf_P (bc_model Q hQ (fun _ => 0)) (bc_policy Q hQ _)).mulVec (fun k => if k=z then 1 else v k) =
      (fun i => (Q i z).toReal) + (bc_kill Q z).mulVec v := by
  funext i
  change (∑ k, (Q i k).toReal * (if k=z then 1 else v k)) = (Q i z).toReal + ∑ k, bc_kill Q z i k * v k
  have he (k : S) : (Q i k).toReal * (if k=z then 1 else v k) =
      (if k=z then (Q i z).toReal else 0) + bc_kill Q z i k * v k := by
    by_cases hk : k=z <;> simp [hk,bc_kill]
  rw [Finset.sum_congr rfl (fun k _ => he k),Finset.sum_add_distrib]
  simp

lemma bc_hitGen_le_one (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 1) (i : S) : bc_hitGen Q z α i ≤ 1 := by
  let v : S → ℝ := fun k => (bc_hitGen Q z α k).toReal
  let y : S → ℝ := fun k => if k=z then 1 else v k
  let P := bf_P (bc_model Q hQ (fun _ => 0)) (bc_policy Q hQ _)
  have he : v = α • P.mulVec y := by
    rw [bc_mask_identity,smul_add]
    exact bc_hitGen_real_rec Q hQ z hα
  have hy : ‖y‖ ≤ max 1 ‖v‖ := by
    apply (pi_norm_le_iff_of_nonneg (le_trans zero_le_one (le_max_left _ _))).mpr
    intro k
    by_cases hk : k=z
    · simpa [y,hk] using le_max_left (1 : ℝ) ‖v‖
    · simpa [y,hk] using (norm_le_pi_norm v k).trans (le_max_right _ _)
  have hn : ‖v‖ ≤ α * max 1 ‖v‖ := by
    calc
      ‖v‖ = α * ‖P.mulVec y‖ := by
        conv_lhs => rw [he]
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos hα.1]
      _ ≤ α * ‖y‖ := mul_le_mul_of_nonneg_left (bf_P_norm _ _ y) hα.1.le
      _ ≤ α * max 1 ‖v‖ := mul_le_mul_of_nonneg_left hy hα.1.le
  have hv : ‖v‖ ≤ 1 := by
    by_contra h
    rw [max_eq_right (le_of_lt (lt_of_not_ge h))] at hn
    nlinarith [norm_nonneg v,hα.2]
  have hi : (bc_hitGen Q z α i).toReal ≤ (1 : ℝ) :=
    (le_abs_self (v i)).trans ((show |v i| = ‖v i‖ from (Real.norm_eq_abs _).symm).le.trans
      ((norm_le_pi_norm v i).trans hv))
  exact (ENNReal.toReal_le_toReal (bc_hitGen_finite Q hQ z hα i) ENNReal.one_ne_top).mp (by simpa using hi)

lemma bc_reachProb_le_one (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z i : S) :
    reachProb Q {z} i ≤ 1 := by
  apply le_of_tendsto (bc_hitGen_limit Q z i)
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from zero_lt_one)] with α hα
  exact bc_hitGen_le_one Q hQ z hα i

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S : Type*} [Fintype S]

lemma bc_green_real_rec (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    (fun i => (bc_green Q α i z).toReal) = (fun i => if i=z then 1 else 0) +
      α • (bf_P (bc_model Q hQ (fun _ => 0)) (bc_policy Q hQ _)).mulVec
        (fun i => (bc_green Q α i z).toReal) := by
  have he := bf_v_equation (bc_model Q hQ (fun i => if i=z then 1 else 0)) (bc_policy Q hQ _) hα
  rw [bf_A,Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec] at he
  have hg : (bf_v (bc_model Q hQ (fun i => if i=z then 1 else 0)) (bc_policy Q hQ _) α) =
      (fun i => (bc_green Q α i z).toReal) := by
    funext i
    rw [bc_green_eq Q hQ]
    rfl
  rw [hg] at he
  funext i
  have hi := congrFun he i
  change (bc_green Q α i z).toReal - α * (∑ k, (Q i k).toReal * (bc_green Q α k z).toReal) =
    ((if i=z then 1 else 0 : ℝ≥0) : ℝ) at hi
  change (bc_green Q α i z).toReal = (if i=z then 1 else 0) +
    α * (∑ k, (Q i k).toReal * (bc_green Q α k z).toReal)
  split_ifs at hi ⊢ <;> norm_num at hi <;> linarith

lemma bc_split_column (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S) (v : S → ℝ) :
    (bf_P (bc_model Q hQ (fun _ => 0)) (bc_policy Q hQ _)).mulVec v =
      (v z) • (fun i => (Q i z).toReal) + (bc_kill Q z).mulVec v := by
  funext i
  change (∑ k, (Q i k).toReal * v k) = v z * (Q i z).toReal + ∑ k, bc_kill Q z i k * v k
  have he (k : S) : (Q i k).toReal * v k =
      (if k=z then v z * (Q i z).toReal else 0) + bc_kill Q z i k * v k := by
    by_cases hk : k=z <;> simp [hk,bc_kill,mul_comm]
  rw [Finset.sum_congr rfl (fun k _ => he k),Finset.sum_add_distrib]
  simp

lemma bc_kill_delta (Q : S → S → ℝ≥0∞) (z : S) :
    (bc_kill Q z).mulVec (fun k => if k=z then (1 : ℝ) else 0) = 0 := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k=z <;> simp [hk,bc_kill]

lemma bc_green_hit_real (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 1) (i : S) :
    (bc_green Q α i z).toReal = (if i=z then 1 else 0) +
      (bc_hitGen Q z α i).toReal * (bc_green Q α z z).toReal := by
  let g : S → ℝ := fun k => (bc_green Q α k z).toReal
  let h : S → ℝ := fun k => (bc_hitGen Q z α k).toReal
  let d : S → ℝ := fun k => if k=z then 1 else 0
  let q : S → ℝ := fun k => (Q k z).toReal
  let K := bc_kill Q z
  have hg : g-d = α • ((g z) • q) + α • K.mulVec (g-d) := by
    have he := bc_green_real_rec Q hQ z hα
    change g = d + α • (bf_P (bc_model Q hQ (fun _ => 0)) (bc_policy Q hQ _)).mulVec g at he
    conv_lhs => rw [he]
    rw [add_sub_cancel_left,bc_split_column Q hQ z g,smul_add]
    change α • ((g z) • q) + α • K.mulVec g = _
    rw [Matrix.mulVec_sub]
    have hz : K.mulVec d = 0 := bc_kill_delta Q z
    rw [hz,sub_zero]
  have hh : (g z) • h = α • ((g z) • q) + α • K.mulVec ((g z) • h) := by
    have he := bc_hitGen_real_rec Q hQ z hα
    change h = α • q + α • K.mulVec h at he
    conv_lhs => rw [he]
    rw [smul_add,Matrix.mulVec_smul]
    simp only [smul_comm (g z) α]
  have hu := bc_substoch_unique K (bc_kill_nonneg Q z) (bc_kill_sum Q hQ z) α hα
    (α • ((g z) • q)) (g-d) ((g z) • h) hg hh
  have hi := congrFun hu i
  change (bc_green Q α i z).toReal = d i + h i * g z
  change g i - d i = g z * h i at hi
  linarith

lemma bc_green_hit (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 1) (i : S) :
    bc_green Q α i z = (if i=z then 1 else 0) + bc_hitGen Q z α i * bc_green Q α z z := by
  apply (ENNReal.toReal_eq_toReal_iff' (bc_green_finite Q hQ hα i z) (by
    apply ENNReal.add_ne_top.mpr
    constructor
    · split_ifs <;> finiteness
    · exact ENNReal.mul_ne_top (bc_hitGen_finite Q hQ z hα i) (bc_green_finite Q hQ hα z z))).mp
  rw [ENNReal.toReal_add (by split_ifs <;> finiteness)
    (ENNReal.mul_ne_top (bc_hitGen_finite Q hQ z hα i) (bc_green_finite Q hQ hα z z)),ENNReal.toReal_mul]
  by_cases hi : i=z <;> simpa [hi] using bc_green_hit_real Q hQ z hα i

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S : Type*} [Fintype S]

lemma bc_cesaro_row (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (i : S) (n : ℕ) (hn : n ≠ 0) :
    (∑ j, (∑ t ∈ Finset.range n, nStep Q t i j) / (n : ℝ≥0∞)) = 1 := by
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul,Finset.sum_comm]
  simp_rw [bc_nStep_sum Q hQ]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast hn) (by finiteness)

lemma bc_projection_row (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (i : S) :
    ∑ j, bc_projection Q hQ i j = 1 := by
  have ht := tendsto_finsetSum Finset.univ (fun j _ => bc_cesaro_limit Q hQ i j)
  have he : (fun n : ℕ => ∑ j, (∑ t ∈ Finset.range n, nStep Q t i j) / (n : ℝ≥0∞)) =ᶠ[atTop] fun _ => 1 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact bc_cesaro_row Q hQ i n (by omega)
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' he.symm)

lemma bc_projection_le_one (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (i j : S) :
    bc_projection Q hQ i j ≤ 1 := by
  rw [← bc_projection_row Q hQ i]
  exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ j)

lemma bc_projection_ne_top (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (i j : S) :
    bc_projection Q hQ i j ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (bc_projection_le_one Q hQ i j)

lemma bc_discount_scale_limit :
    Tendsto (fun α : ℝ => ENNReal.ofReal (1-α)) (𝓝[<] 1) (𝓝 0) := by
  have ht : Tendsto (fun α : ℝ => 1-α) (𝓝[<] 1) (𝓝 0) := by
    simpa using (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds) :
      Tendsto (fun α : ℝ => 1-α) (𝓝[<] 1) (𝓝 (1-1)))
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht

lemma bc_projection_hit (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z i : S) :
    bc_projection Q hQ i z = reachProb Q {z} i * bc_projection Q hQ z z := by
  have hr : reachProb Q {z} i ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (bc_reachProb_le_one Q hQ z i)
  have hm := ENNReal.Tendsto.mul (bc_hitGen_limit Q z i) (Or.inr (bc_projection_ne_top Q hQ z z))
    (bc_green_limit Q hQ z z) (Or.inr hr)
  have hd : Tendsto (fun α : ℝ => ENNReal.ofReal (1-α) * (if i=z then 1 else 0)) (𝓝[<] 1) (𝓝 0) := by
    by_cases hi : i=z
    · simpa [hi] using bc_discount_scale_limit
    · simpa [hi] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ≥0∞)) (𝓝[<] 1) (𝓝 0))
  have he : (fun α : ℝ => ENNReal.ofReal (1-α) * bc_green Q α i z) =ᶠ[𝓝[<] 1]
      (fun α => ENNReal.ofReal (1-α) * (if i=z then 1 else 0) +
        bc_hitGen Q z α i * (ENNReal.ofReal (1-α) * bc_green Q α z z)) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from zero_lt_one)] with α hα
    rw [bc_green_hit Q hQ z hα i,mul_add]
    congr 1
    ring
  have hs := hd.add hm
  simp only [zero_add] at hs
  exact tendsto_nhds_unique (bc_green_limit Q hQ i z) (hs.congr' he.symm)

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section

def bc_tail (u : ℕ → ℝ≥0∞) (k : ℕ) : ℝ≥0∞ := ∑' n : ℕ, if k < n then u n else 0

lemma bc_series_tail (u : ℕ → ℝ≥0∞) (α : ℝ) :
    bc_series (bc_tail u) α = ∑' n : ℕ, u n * ∑ k ∈ Finset.range n, ENNReal.ofReal α ^ k := by
  unfold bc_series bc_tail
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro n
  rw [tsum_eq_sum (s := Finset.range n) (fun k hk => by
    have hn : ¬ k < n := by simpa using hk
    simp [hn])]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp [Finset.mem_range.mp hk,mul_comm]

lemma bc_tail_mass (u : ℕ → ℝ≥0∞) : ∑' k, bc_tail u k = ∑' n : ℕ, (n : ℝ≥0∞) * u n := by
  have ht := bc_series_tail u 1
  simpa [bc_series,ENNReal.ofReal_one,one_pow,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_comm] using ht

lemma bc_geom_balance {α : ℝ} (hα : α ∈ Set.Ioo 0 1) (n : ℕ) :
    ENNReal.ofReal α ^ n + ENNReal.ofReal (1-α) * (∑ k ∈ Finset.range n, ENNReal.ofReal α ^ k) = 1 := by
  have hr : α^n + (1-α) * (∑ k ∈ Finset.range n, α^k) = 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ,pow_succ]
      calc
        α^n * α + (1-α) * ((∑ k ∈ Finset.range n, α^k) + α^n) =
          α^n + (1-α) * (∑ k ∈ Finset.range n, α^k) := by ring
        _ = 1 := ih
  have he := congrArg ENNReal.ofReal hr
  rw [ENNReal.ofReal_add (pow_nonneg hα.1.le n) (mul_nonneg (sub_nonneg.mpr hα.2.le) (Finset.sum_nonneg (fun k _ => pow_nonneg hα.1.le k))),
    ENNReal.ofReal_mul (sub_nonneg.mpr hα.2.le),ENNReal.ofReal_sum_of_nonneg (fun k _ => pow_nonneg hα.1.le k)] at he
  simpa only [ENNReal.ofReal_pow hα.1.le,ENNReal.ofReal_one] using he

lemma bc_renewal_balance (u : ℕ → ℝ≥0∞) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    bc_series u α + ENNReal.ofReal (1-α) * bc_series (bc_tail u) α = ∑' n, u n := by
  rw [bc_series_tail,← ENNReal.tsum_mul_left]
  unfold bc_series
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro n
  calc
    ENNReal.ofReal α ^ n * u n + ENNReal.ofReal (1-α) * (u n * ∑ k ∈ Finset.range n, ENNReal.ofReal α ^ k) =
      (ENNReal.ofReal α ^ n + ENNReal.ofReal (1-α) * ∑ k ∈ Finset.range n, ENNReal.ofReal α ^ k) * u n := by ring
    _ = u n := by rw [bc_geom_balance hα,one_mul]

variable {S : Type*} [Fintype S]

lemma bc_projection_diagonal_hit (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    (hp : bc_projection Q hQ z z ≠ 0) : reachProb Q {z} z = 1 := by
  have he := bc_projection_hit Q hQ z z
  exact (ENNReal.mul_left_inj hp (bc_projection_ne_top Q hQ z z)).mp (by simpa using he.symm)

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S : Type*} [Fintype S]

lemma bc_green_renewal_inv (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    (hr : reachProb Q {z} z = 1) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    ENNReal.ofReal (1-α) * bc_green Q α z z =
      (bc_series (bc_tail (fun t => firstPassage Q {z} t z)) α)⁻¹ := by
  let H := bc_hitGen Q z α z
  let D := bc_series (bc_tail (fun t => firstPassage Q {z} t z)) α
  let G := bc_green Q α z z
  let a := ENNReal.ofReal (1-α)
  have ha : a ≠ 0 := by dsimp [a]; exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hα.2)).ne'
  have hb : H + a * D = 1 := by
    have he := bc_renewal_balance (fun t => firstPassage Q {z} t z) hα
    change H + a * D = reachProb Q {z} z at he
    rwa [hr] at he
  have hD : D ≠ ⊤ := by
    intro ht
    rw [ht,ENNReal.mul_top ha,add_top] at hb
    exact ENNReal.top_ne_one hb
  have hH : H ≠ ⊤ := bc_hitGen_finite Q hQ z hα z
  have hG : G ≠ ⊤ := bc_green_finite Q hQ hα z z
  have hbR : H.toReal + (1-α) * D.toReal = 1 := by
    have he := congrArg ENNReal.toReal hb
    rw [ENNReal.toReal_add hH (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hD),ENNReal.toReal_mul] at he
    simpa [a,ENNReal.toReal_ofReal (sub_nonneg.mpr hα.2.le)] using he
  have hgR : G.toReal = 1 + H.toReal * G.toReal := by
    simpa only [H,G,ite_true] using bc_green_hit_real Q hQ z hα z
  have heR : (1-α) * G.toReal * D.toReal = 1 := by
    have he := congrArg (fun x : ℝ => x * G.toReal) hbR
    nlinarith
  have he : (a * G) * D = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG) hD) ENNReal.one_ne_top).mp
    rw [ENNReal.toReal_mul,ENNReal.toReal_mul]
    simpa [a,ENNReal.toReal_ofReal (sub_nonneg.mpr hα.2.le)] using heR
  exact ENNReal.eq_inv_of_mul_eq_one_left he

lemma bc_projection_steady (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S) :
    bc_projection Q hQ z z = steadyState Q z := by
  by_cases hr : reachProb Q {z} z = 1
  · have ht := bc_series_left_limit (bc_tail (fun t => firstPassage Q {z} t z))
    rw [bc_tail_mass] at ht
    have hi := tendsto_inv_iff.2 ht
    have he : (fun α : ℝ => ENNReal.ofReal (1-α) * bc_green Q α z z) =ᶠ[𝓝[<] 1]
        (fun α => (bc_series (bc_tail (fun t => firstPassage Q {z} t z)) α)⁻¹) := by
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from zero_lt_one)] with α hα
      exact bc_green_renewal_inv Q hQ z hr hα
    have hp := tendsto_nhds_unique (bc_green_limit Q hQ z z) (hi.congr' he.symm)
    simpa only [steadyState,meanPassage,if_pos hr] using hp
  · have hp : bc_projection Q hQ z z = 0 := by
      by_contra h
      exact hr (bc_projection_diagonal_hit Q hQ z h)
    simp [hp,steadyState,meanPassage,hr]

lemma bc_positive_iff_projection (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S) :
    PositiveRecurrent Q z ↔ bc_projection Q hQ z z ≠ 0 := by
  constructor
  · intro hz
    rw [bc_projection_steady,steadyState]
    simpa using hz.2
  · intro hp
    constructor
    · exact bc_projection_diagonal_hit Q hQ z hp
    · rw [bc_projection_steady,steadyState] at hp
      simpa using hp

lemma bc_projection_factor (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z i : S) :
    bc_projection Q hQ i z = reachProb Q {z} i * steadyState Q z := by
  rw [bc_projection_hit,bc_projection_steady]

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S : Type*} [Fintype S]

lemma bc_firstPass_le_nStep (Q : S → S → ℝ≥0∞) (z : S) (n : ℕ) (i : S) :
    firstPassage Q {z} n i ≤ nStep Q n i z := by
  induction n generalizing i with
  | zero => simp [firstPassage]
  | succ n ih =>
    rw [bc_firstPass_step,bc_nStep_backward]
    cases n with
    | zero => simp [firstPassage,nStep]
    | succ n =>
      simp only [Nat.succ_ne_zero,if_false,zero_add]
      apply Finset.sum_le_sum
      intro k _
      split_ifs
      · exact bot_le
      · exact mul_le_mul' le_rfl (ih k)

lemma bc_reach_leads (Q : S → S → ℝ≥0∞) (z i : S) (hr : reachProb Q {z} i ≠ 0) : LeadsTo Q i z := by
  by_contra h
  have hn : ∀ n, nStep Q n i z = 0 := by simpa only [LeadsTo,not_exists,not_not] using h
  have hf : ∀ n, firstPassage Q {z} n i = 0 := fun n => le_antisymm ((bc_firstPass_le_nStep Q z n i).trans_eq (hn n)) bot_le
  apply hr
  simp [reachProb,hf]

lemma bc_hitGen_toReal_limit (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z i : S) :
    Tendsto (fun α : ℝ => (bc_hitGen Q z α i).toReal) (𝓝[<] 1) (𝓝 (reachProb Q {z} i).toReal) := by
  exact (ENNReal.tendsto_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (bc_reachProb_le_one Q hQ z i))).comp (bc_hitGen_limit Q z i)

lemma bc_reach_real_rec (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z i : S) :
    (reachProb Q {z} i).toReal = (Q i z).toReal + ∑ k, bc_kill Q z i k * (reachProb Q {z} k).toReal := by
  have hα : Tendsto (fun α : ℝ => α) (𝓝[<] 1) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
  have ht := (hα.mul (tendsto_const_nhds (x := (Q i z).toReal))).add
    (hα.mul (tendsto_finsetSum Finset.univ (fun k _ =>
      (tendsto_const_nhds (x := bc_kill Q z i k)).mul (bc_hitGen_toReal_limit Q hQ z k))))
  simp only [one_mul] at ht
  have he : (fun α : ℝ => (bc_hitGen Q z α i).toReal) =ᶠ[𝓝[<] 1]
      (fun α => α * (Q i z).toReal + α * ∑ k, bc_kill Q z i k * (bc_hitGen Q z α k).toReal) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from zero_lt_one)] with α hα
    exact congrFun (bc_hitGen_real_rec Q hQ z hα) i
  exact tendsto_nhds_unique (bc_hitGen_toReal_limit Q hQ z i) (ht.congr' he.symm)

lemma bc_recurrent_harmonic (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    (hz : reachProb Q {z} z = 1) :
    (bf_P (bc_model Q hQ (fun _ => 0)) (bc_policy Q hQ _)).mulVec (fun k => (reachProb Q {z} k).toReal) =
      (fun k => (reachProb Q {z} k).toReal) := by
  let r : S → ℝ := fun k => (reachProb Q {z} k).toReal
  have hrz : r z = 1 := by simp [r,hz]
  have hm : (fun k => if k=z then 1 else r k) = r := by
    funext k
    by_cases hk : k=z <;> simp [hk,hrz]
  have he := bc_mask_identity Q hQ z r
  rw [hm] at he
  rw [he]
  funext i
  exact (bc_reach_real_rec Q hQ z i).symm

lemma bc_real_nStep_harmonic (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (r : S → ℝ)
    (hr : ∀ i, ∑ j, (Q i j).toReal * r j = r i) (n : ℕ) (i : S) :
    ∑ j, (nStep Q n i j).toReal * r j = r i := by
  induction n generalizing i with
  | zero =>
    have he (j : S) : (if i=j then (1 : ℝ≥0∞) else 0).toReal * r j = if i=j then r j else 0 := by
      by_cases h : i=j <;> simp [h]
    simp_rw [nStep,he]
    simp
  | succ n ih =>
    simp_rw [bc_nStep_backward,ENNReal.toReal_sum (fun k _ => ENNReal.mul_ne_top
      (bc_Q_ne_top Q hQ i k) (ne_top_of_le_ne_top ENNReal.one_ne_top (bc_nStep_le_one Q hQ n k _))),ENNReal.toReal_mul,Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc,← Finset.mul_sum,ih]
    exact hr i

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S : Type*} [Fintype S]

lemma bc_average_eq_one (p v : S → ℝ) (hp : ∀ j, 0 ≤ p j) (hrow : ∑ j, p j = 1)
    (hv : ∀ j, v j ≤ 1) (he : ∑ j, p j * v j = 1) (j : S) (hj : p j ≠ 0) : v j = 1 := by
  have hs : ∑ k, p k * (1-v k) = 0 := by
    simp_rw [mul_sub,mul_one]
    rw [Finset.sum_sub_distrib,hrow,he,sub_self]
  have hl : p j * (1-v j) ≤ 0 := by
    rw [← hs]
    exact Finset.single_le_sum (fun k _ => mul_nonneg (hp k) (sub_nonneg.mpr (hv k))) (Finset.mem_univ j)
  have hz : p j * (1-v j) = 0 := le_antisymm hl (mul_nonneg (hp j) (sub_nonneg.mpr (hv j)))
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hj) |>.symm

lemma bc_nStep_real_sum (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (n : ℕ) (i : S) :
    ∑ j, (nStep Q n i j).toReal = 1 := by
  have he := congrArg ENNReal.toReal (bc_nStep_sum Q hQ n i)
  rw [ENNReal.toReal_sum (fun j _ => ne_top_of_le_ne_top ENNReal.one_ne_top (bc_nStep_le_one Q hQ n i j))] at he
  simpa using he

lemma bc_recurrent_reachable_hit_one (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    (hz : reachProb Q {z} z = 1) (j : S) (hj : LeadsTo Q z j) : reachProb Q {z} j = 1 := by
  obtain ⟨n,hn⟩ := hj
  let r : S → ℝ := fun k => (reachProb Q {z} k).toReal
  have hv : ∀ k, r k ≤ 1 := by
    intro k
    exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (bc_reachProb_le_one Q hQ z k)) ENNReal.one_ne_top).mpr (bc_reachProb_le_one Q hQ z k)
  have hh : ∀ i, ∑ k, (Q i k).toReal * r k = r i := fun i => congrFun (bc_recurrent_harmonic Q hQ z hz) i
  have he := bc_real_nStep_harmonic Q hQ r hh n z
  have hrz : r z = 1 := by simp [r,hz]
  rw [hrz] at he
  have hnj : (nStep Q n z j).toReal ≠ 0 := by
    exact ENNReal.toReal_ne_zero.mpr ⟨hn,ne_top_of_le_ne_top ENNReal.one_ne_top (bc_nStep_le_one Q hQ n z j)⟩
  have hreal := bc_average_eq_one (fun k => (nStep Q n z k).toReal) r (fun _ => ENNReal.toReal_nonneg)
    (bc_nStep_real_sum Q hQ n z) hv he j hnj
  exact (ENNReal.toReal_eq_toReal_iff' (ne_top_of_le_ne_top ENNReal.one_ne_top (bc_reachProb_le_one Q hQ z j)) ENNReal.one_ne_top).mp (by simpa using hreal)

lemma bc_recurrent_reachable_communicates (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    (hz : reachProb Q {z} z = 1) (j : S) (hj : LeadsTo Q z j) : j ∈ commClass Q z := by
  exact ⟨hj,bc_reach_leads Q z j (by rw [bc_recurrent_reachable_hit_one Q hQ z hz j hj]; exact one_ne_zero)⟩

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S : Type*} [Fintype S]

lemma bc_green_forward (Q : S → S → ℝ≥0∞) (α : ℝ) (i j : S) :
    bc_green Q α i j = (if i=j then 1 else 0) +
      ENNReal.ofReal α * ∑ k, bc_green Q α i k * Q k j := by
  unfold bc_green
  rw [tsum_eq_zero_add' ENNReal.summable]
  have hz : nStep Q 0 i j = (if i=j then 1 else 0) := rfl
  have hs (n : ℕ) : nStep Q (n+1) i j = ∑ k, nStep Q n i k * Q k j := rfl
  simp only [pow_zero,hz,one_mul]
  simp_rw [hs,pow_succ]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro k _
  rw [← ENNReal.tsum_mul_right,← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro n
  ring

lemma bc_projection_invariant (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (i j : S) :
    ∑ k, bc_projection Q hQ i k * Q k j = bc_projection Q hQ i j := by
  have hα : Tendsto (fun α : ℝ => ENNReal.ofReal α) (𝓝[<] 1) (𝓝 1) := by
    simpa only [Function.comp_def,id_eq,ENNReal.ofReal_one] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun α : ℝ => α) (𝓝[<] 1) (𝓝 1))
  have hs := tendsto_finsetSum Finset.univ (fun k _ => ENNReal.Tendsto.mul_const (bc_green_limit Q hQ i k) (Or.inr (bc_Q_ne_top Q hQ k j)))
  have hm := ENNReal.Tendsto.mul hα (Or.inl one_ne_zero) hs (Or.inr ENNReal.one_ne_top)
  simp only [one_mul] at hm
  have hd : Tendsto (fun α : ℝ => ENNReal.ofReal (1-α) * (if i=j then 1 else 0)) (𝓝[<] 1) (𝓝 0) := by
    by_cases hij : i=j
    · simpa [hij] using bc_discount_scale_limit
    · simpa [hij] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ≥0∞)) (𝓝[<] 1) (𝓝 0))
  have he : (fun α : ℝ => ENNReal.ofReal (1-α) * bc_green Q α i j) =ᶠ[𝓝[<] 1]
      (fun α => ENNReal.ofReal (1-α) * (if i=j then 1 else 0) +
        ENNReal.ofReal α * ∑ k, (ENNReal.ofReal (1-α) * bc_green Q α i k) * Q k j) := by
    filter_upwards [] with α
    rw [bc_green_forward,mul_add]
    simp_rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hl := hd.add hm
  simp only [zero_add] at hl
  exact (tendsto_nhds_unique (bc_green_limit Q hQ i j) (hl.congr' he.symm)).symm

lemma bc_projection_nStep_invariant (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (n : ℕ) (i j : S) :
    ∑ k, bc_projection Q hQ i k * nStep Q n k j = bc_projection Q hQ i j := by
  induction n with
  | zero => simp [nStep]
  | succ n ih =>
    simp_rw [bc_nStep_backward,Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc,← Finset.sum_mul,bc_projection_invariant Q hQ]
    exact ih

lemma bc_reachable_positive (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    (hz : PositiveRecurrent Q z) (j : S) (hj : LeadsTo Q z j) : PositiveRecurrent Q j := by
  obtain ⟨n,hn⟩ := hj
  have hp := (bc_positive_iff_projection Q hQ z).mp hz
  have hprod : bc_projection Q hQ z z * nStep Q n z j ≠ 0 := mul_ne_zero hp hn
  have hle : bc_projection Q hQ z z * nStep Q n z j ≤ bc_projection Q hQ z j := by
    rw [← bc_projection_nStep_invariant Q hQ n z j]
    exact Finset.single_le_sum (f := fun k => bc_projection Q hQ z k * nStep Q n k j)
      (fun _ _ => bot_le) (Finset.mem_univ z)
  have hcol : bc_projection Q hQ z j ≠ 0 := by intro he; exact hprod (le_antisymm (hle.trans_eq he) bot_le)
  apply (bc_positive_iff_projection Q hQ j).mpr
  intro he
  rw [bc_projection_hit Q hQ j z,he,mul_zero] at hcol
  exact hcol rfl

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S : Type*} [Fintype S]

def bc_pass_partial (Q : S → S → ℝ≥0∞) (z : S) (n : ℕ) (i : S) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range (n+1), firstPassage Q {z} t i

lemma bc_pass_partial_rec (Q : S → S → ℝ≥0∞) (z : S) (n : ℕ) (i : S) :
    bc_pass_partial Q z (n+1) i = Q i z + ∑ k, if k=z then 0 else Q i k * bc_pass_partial Q z n k := by
  unfold bc_pass_partial
  rw [Finset.sum_range_succ']
  have hz : firstPassage Q {z} 0 i = 0 := rfl
  simp only [hz,add_zero]
  simp_rw [bc_firstPass_step,Finset.sum_add_distrib]
  have he : (∑ t ∈ Finset.range (n+1), if t=0 then Q i z else 0) = Q i z := by simp
  rw [he,Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k=z
  · simp [hk]
  · simp only [hk,if_false,Finset.mul_sum]

lemma bc_reach_minimal (Q : S → S → ℝ≥0∞) (z : S) (g : S → ℝ≥0∞)
    (hg : ∀ i, Q i z + (∑ k, if k=z then 0 else Q i k * g k) ≤ g i) (i : S) :
    reachProb Q {z} i ≤ g i := by
  have hp : ∀ n i, bc_pass_partial Q z n i ≤ g i := by
    intro n
    induction n with
    | zero => intro i; simp [bc_pass_partial,firstPassage]
    | succ n ih =>
      intro i
      rw [bc_pass_partial_rec]
      apply le_trans _ (hg i)
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro k _
      split_ifs
      · exact le_rfl
      · exact mul_le_mul' le_rfl (ih k)
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  cases n with
  | zero => simp
  | succ n => exact hp n i

lemma bc_recurrent_harmonic_enn (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    (hz : reachProb Q {z} z = 1) (i : S) : ∑ k, Q i k * reachProb Q {z} k = reachProb Q {z} i := by
  have hf k : Q i k * reachProb Q {z} k ≠ ⊤ := ENNReal.mul_ne_top (bc_Q_ne_top Q hQ i k)
    (ne_top_of_le_ne_top ENNReal.one_ne_top (bc_reachProb_le_one Q hQ z k))
  apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.sum_ne_top.mpr (fun k _ => hf k))
    (ne_top_of_le_ne_top ENNReal.one_ne_top (bc_reachProb_le_one Q hQ z i))).mp
  rw [ENNReal.toReal_sum (fun k _ => hf k)]
  simp_rw [ENNReal.toReal_mul]
  exact congrFun (bc_recurrent_harmonic Q hQ z hz) i

lemma bc_harmonic_boundary_rec (Q : S → S → ℝ≥0∞) (z : S) (g : S → ℝ≥0∞)
    (hr : ∀ i, ∑ k, Q i k * g k = g i) (hz : g z = 1) (i : S) :
    Q i z + (∑ k, if k=z then 0 else Q i k * g k) = g i := by
  have ht k : Q i k * g k = (if k=z then Q i z else 0) + (if k=z then 0 else Q i k * g k) := by
    by_cases hk : k=z <;> simp [hk,hz]
  rw [← hr i,Finset.sum_congr rfl (fun k _ => ht k),Finset.sum_add_distrib]
  simp

lemma bc_class_reach_equal (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    (hz : PositiveRecurrent Q z) (j : S) (hj : j ∈ commClass Q z) (i : S) :
    reachProb Q {z} i = reachProb Q {j} i := by
  have hjp := bc_reachable_positive Q hQ z hz j hj.1
  have hjz : reachProb Q {j} z = 1 := bc_recurrent_reachable_hit_one Q hQ j hjp.1 z hj.2
  have hzj : reachProb Q {z} j = 1 := bc_recurrent_reachable_hit_one Q hQ z hz.1 j hj.1
  apply le_antisymm
  · exact bc_reach_minimal Q z (fun k => reachProb Q {j} k)
      (fun k => (bc_harmonic_boundary_rec Q z _ (bc_recurrent_harmonic_enn Q hQ j hjp.1) hjz k).le) i
  · exact bc_reach_minimal Q j (fun k => reachProb Q {z} k)
      (fun k => (bc_harmonic_boundary_rec Q j _ (bc_recurrent_harmonic_enn Q hQ z hz.1) hzj k).le) i

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S : Type*} [Fintype S]

lemma bc_leads_refl (Q : S → S → ℝ≥0∞) (i : S) : LeadsTo Q i i := ⟨0,by simp [nStep]⟩

lemma bc_nStep_add (Q : S → S → ℝ≥0∞) (n m : ℕ) (i j : S) :
    nStep Q (n+m) i j = ∑ k, nStep Q n i k * nStep Q m k j := by
  change Matrix.of (nStep Q (n+m)) i j = _
  rw [bc_nStep_pow,pow_add,← bc_nStep_pow,← bc_nStep_pow]
  rfl

lemma bc_leads_trans (Q : S → S → ℝ≥0∞) {i j k : S} (hij : LeadsTo Q i j) (hjk : LeadsTo Q j k) : LeadsTo Q i k := by
  obtain ⟨n,hn⟩ := hij
  obtain ⟨m,hm⟩ := hjk
  refine ⟨n+m,?_⟩
  have he := mul_ne_zero hn hm
  have hl : nStep Q n i j * nStep Q m j k ≤ nStep Q (n+m) i k := by
    rw [bc_nStep_add]
    exact Finset.single_le_sum (f := fun l => nStep Q n i l * nStep Q m l k) (fun _ _ => bot_le) (Finset.mem_univ j)
  intro hz
  exact he (le_antisymm (hl.trans_eq hz) bot_le)

lemma bc_leads_edge (Q : S → S → ℝ≥0∞) {i j : S} (hij : Q i j ≠ 0) : LeadsTo Q i j := by
  refine ⟨1,?_⟩
  simpa [nStep] using hij

lemma bc_class_closed (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    (hz : PositiveRecurrent Q z) {i j : S} (hi : i ∈ commClass Q z) (hij : Q i j ≠ 0) : j ∈ commClass Q z :=
  bc_recurrent_reachable_communicates Q hQ z hz.1 j (bc_leads_trans Q hi.1 (bc_leads_edge Q hij))

lemma bc_projection_class_row (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    (hz : PositiveRecurrent Q z) (j : S) :
    bc_projection Q hQ z j = if j ∈ commClass Q z then steadyState Q j else 0 := by
  by_cases hj : j ∈ commClass Q z
  · have hjp := bc_reachable_positive Q hQ z hz j hj.1
    have hr := bc_recurrent_reachable_hit_one Q hQ j hjp.1 z hj.2
    rw [if_pos hj,bc_projection_factor,hr,one_mul]
  · rw [if_neg hj]
    by_contra hp
    have hreach : reachProb Q {j} z ≠ 0 := by
      intro he
      rw [bc_projection_factor,he,zero_mul] at hp
      exact hp rfl
    exact hj (bc_recurrent_reachable_communicates Q hQ z hz.1 j (bc_reach_leads Q j z hreach))

lemma bc_class_steady_sum (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    (hz : PositiveRecurrent Q z) : ∑ j ∈ Finset.univ.filter (fun j => j ∈ commClass Q z), steadyState Q j = 1 := by
  have he := bc_projection_row Q hQ z
  simp_rw [bc_projection_class_row Q hQ z hz] at he
  simpa only [Finset.sum_filter] using he

lemma bc_distinguished_reach_zero (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (Z : Finset S)
    (hZ : IsDistinguishedSet Q Z) {z z' : S} (hz : z ∈ Z) (hz' : z' ∈ Z) (hne : z ≠ z') :
    reachProb Q {z} z' = 0 := by
  by_contra hr
  have hc := bc_recurrent_reachable_communicates Q hQ z' (hZ.1 z' hz').1 z (bc_reach_leads Q z z' hr)
  exact hZ.2.1 z hz z' hz' hne ⟨hc.2,hc.1⟩

lemma bc_class_disjoint (Q : S → S → ℝ≥0∞) (Z : Finset S) (hZ : IsDistinguishedSet Q Z)
    {z z' : S} (hz : z ∈ Z) (hz' : z' ∈ Z) (hne : z ≠ z') :
    Disjoint (commClass Q z) (commClass Q z') := by
  apply Set.disjoint_left.mpr
  intro j hj hj'
  exact hZ.2.1 z hz z' hz' hne ⟨bc_leads_trans Q hj.1 hj'.2,bc_leads_trans Q hj'.1 hj.2⟩

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S : Type*} [Fintype S]

lemma bc_projection_distinguished (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (Z : Finset S)
    (hZ : IsDistinguishedSet Q Z) (i j : S) :
    bc_projection Q hQ i j = ∑ z ∈ Z, reachProb Q {z} i * bc_projection Q hQ z j := by
  by_cases hp : steadyState Q j = 0
  · rw [bc_projection_factor,hp,mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro z _
    rw [bc_projection_factor,hp,mul_zero,mul_zero]
  · have hjp : PositiveRecurrent Q j := (bc_positive_iff_projection Q hQ j).mpr (by rwa [bc_projection_steady])
    obtain ⟨z,hz,hjz⟩ := hZ.2.2 j hjp
    rw [Finset.sum_eq_single z]
    · rw [bc_projection_class_row Q hQ z (hZ.1 z hz),if_pos hjz,bc_projection_factor,
        bc_class_reach_equal Q hQ z (hZ.1 z hz) j hjz i]
    · intro z' hz' hne
      have hnot : j ∉ commClass Q z' := by
        intro hc
        exact Set.disjoint_left.mp (bc_class_disjoint Q Z hZ hz hz' hne.symm) hjz hc
      rw [bc_projection_class_row Q hQ z' (hZ.1 z' hz'),if_neg hnot,mul_zero]
    · intro hnot
      exact False.elim (hnot hz)

lemma bc_distinguished_mass (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (Z : Finset S)
    (hZ : IsDistinguishedSet Q Z) (i : S) : ∑ z ∈ Z, reachProb Q {z} i = 1 := by
  have he := bc_projection_row Q hQ i
  simp_rw [bc_projection_distinguished Q hQ Z hZ i] at he
  rw [Finset.sum_comm] at he
  simp_rw [← Finset.mul_sum,bc_projection_row Q hQ,mul_one] at he
  exact he

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S : Type*} [Fintype S]

lemma bc_firstPass_set_step (Q : S → S → ℝ≥0∞) (G : Set S) (n : ℕ) (i : S) :
    firstPassage Q G (n+1) i = (if n=0 then ∑ k, if k ∈ G then Q i k else 0 else 0) +
      ∑ k, if k ∈ G then 0 else Q i k * firstPassage Q G n k := by
  cases n with
  | zero => simp [firstPassage]
  | succ n => simp [firstPassage]

def bc_set_partial (Q : S → S → ℝ≥0∞) (G : Set S) (n : ℕ) (i : S) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range (n+1), firstPassage Q G t i

lemma bc_set_partial_rec (Q : S → S → ℝ≥0∞) (G : Set S) (n : ℕ) (i : S) :
    bc_set_partial Q G (n+1) i = (∑ k, if k ∈ G then Q i k else 0) +
      ∑ k, if k ∈ G then 0 else Q i k * bc_set_partial Q G n k := by
  unfold bc_set_partial
  rw [Finset.sum_range_succ']
  have hz : firstPassage Q G 0 i = 0 := rfl
  simp only [hz,add_zero]
  simp_rw [bc_firstPass_set_step,Finset.sum_add_distrib]
  have he : (∑ t ∈ Finset.range (n+1), if t=0 then ∑ k, if k ∈ G then Q i k else 0 else 0) =
      ∑ k, if k ∈ G then Q i k else 0 := by simp
  rw [he,Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k ∈ G
  · simp [hk]
  · simp only [hk,if_false,Finset.mul_sum]

lemma bc_reach_set_minimal (Q : S → S → ℝ≥0∞) (G : Set S) (g : S → ℝ≥0∞)
    (hg : ∀ i, (∑ k, if k ∈ G then Q i k else 0) + (∑ k, if k ∈ G then 0 else Q i k * g k) ≤ g i) (i : S) :
    reachProb Q G i ≤ g i := by
  have hp : ∀ n i, bc_set_partial Q G n i ≤ g i := by
    intro n
    induction n with
    | zero => intro i; simp [bc_set_partial,firstPassage]
    | succ n ih =>
      intro i
      rw [bc_set_partial_rec]
      apply le_trans _ (hg i)
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro k _
      split_ifs
      · exact le_rfl
      · exact mul_le_mul' le_rfl (ih k)
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  cases n with
  | zero => simp
  | succ n => exact hp n i

lemma bc_reach_set_le_one (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (G : Set S) (i : S) :
    reachProb Q G i ≤ 1 := by
  apply bc_reach_set_minimal Q G (fun _ => 1)
  intro i
  simp only [mul_one]
  rw [← Finset.sum_add_distrib]
  have he : (∑ k, ((if k ∈ G then Q i k else 0) + (if k ∈ G then 0 else Q i k))) = 1 := by
    rw [← hQ i]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp
  exact he.le

lemma bc_reach_set_rec (Q : S → S → ℝ≥0∞) (G : Set S) (i : S) :
    reachProb Q G i = (∑ k, if k ∈ G then Q i k else 0) +
      ∑ k, if k ∈ G then 0 else Q i k * reachProb Q G k := by
  unfold reachProb
  rw [tsum_eq_zero_add' ENNReal.summable]
  have hz : firstPassage Q G 0 i = 0 := rfl
  simp only [hz,zero_add]
  simp_rw [bc_firstPass_set_step,ENNReal.tsum_add]
  have he : (∑' n : ℕ, if n=0 then ∑ k, if k ∈ G then Q i k else 0 else 0) =
      ∑ k, if k ∈ G then Q i k else 0 := by
    rw [tsum_eq_single 0]
    · simp
    · intro n hn; simp [hn]
  rw [he,Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k ∈ G
  · simp [hk]
  · simp only [hk,if_false,ENNReal.tsum_mul_left]

lemma bc_reach_set_closed_boundary (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (G : Set S)
    (hclosed : ∀ i ∈ G, ∀ j, Q i j ≠ 0 → j ∈ G) (i : S) (hi : i ∈ G) : reachProb Q G i = 1 := by
  have hfirst : firstPassage Q G 1 i = 1 := by
    change (∑ k, if k ∈ G then Q i k else 0) = 1
    rw [← hQ i]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k ∈ G
    · simp [hk]
    · have hzero : Q i k = 0 := by by_contra h; exact hk (hclosed i hi k h)
      simp [hk,hzero]
  apply le_antisymm (bc_reach_set_le_one Q hQ G i)
  rw [← hfirst]
  exact ENNReal.le_tsum 1

lemma bc_reach_set_harmonic (Q : S → S → ℝ≥0∞) (G : Set S)
    (hb : ∀ j ∈ G, reachProb Q G j = 1) (i : S) :
    ∑ k, Q i k * reachProb Q G k = reachProb Q G i := by
  rw [bc_reach_set_rec,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k ∈ G
  · simp [hk,hb k hk]
  · simp [hk]

lemma bc_harmonic_set_boundary_rec (Q : S → S → ℝ≥0∞) (G : Set S) (g : S → ℝ≥0∞)
    (hr : ∀ i, ∑ k, Q i k * g k = g i) (hb : ∀ j ∈ G, g j = 1) (i : S) :
    (∑ k, if k ∈ G then Q i k else 0) + (∑ k, if k ∈ G then 0 else Q i k * g k) = g i := by
  rw [← hr i,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k ∈ G
  · simp [hk,hb k hk]
  · simp [hk]

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section

lemma bc_meromorphic_extension (f : ℝ → ℝ) (hm : MeromorphicAt f 1) (B : ℝ)
    (hb : ∀ᶠ α : ℝ in 𝓝[<] 1, ‖f α‖ ≤ B) :
    ∃ g : ℝ → ℝ, AnalyticAt ℝ g 1 ∧ f =ᶠ[𝓝[<] 1] g := by
  have hle : 𝓝[<] (1 : ℝ) ≤ 𝓝[≠] (1 : ℝ) := nhdsLT_le_nhdsNE _
  have ho : 0 ≤ meromorphicOrderAt f 1 := by
    by_contra h
    have ht := (tendsto_cobounded_of_meromorphicOrderAt_neg (lt_of_not_ge h)).mono_left hle
    have hn := tendsto_norm_atTop_iff_cobounded.mpr ht
    obtain ⟨α,hbα,hα⟩ := (hb.and (hn.eventually (eventually_gt_atTop (B+1)))).exists
    linarith
  obtain ⟨g,hg,he⟩ := hm.meromorphicOrderAt_nonneg_iff.mp ho
  exact ⟨g,hg,he.filter_mono hle⟩

variable {S : Type*} [Fintype S]

lemma bc_hitGen_analytic_extension (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z i : S) :
    ∃ g : ℝ → ℝ, AnalyticAt ℝ g 1 ∧
      (fun α : ℝ => (bc_hitGen Q z α i).toReal) =ᶠ[𝓝[<] 1] g ∧ g 1 = (reachProb Q {z} i).toReal := by
  let M := bc_model Q hQ (fun k => if k=z then 1 else 0)
  let e := bc_policy Q hQ (fun k => if k=z then 1 else 0)
  obtain ⟨p,q,hp⟩ := bf_rational_data M e i
  obtain ⟨r,s,hr⟩ := bf_rational_data M e z
  let F : ℝ → ℝ := fun α => (p.eval α / q.eval α - (if i=z then 1 else 0)) / (r.eval α / s.eval α)
  have hpoly (v : Polynomial ℝ) : MeromorphicAt (fun α : ℝ => v.eval α) 1 :=
    ((AnalyticOnNhd.eval_polynomial v) 1 (Set.mem_univ 1)).meromorphicAt
  have hm : MeromorphicAt F 1 := ((hpoly p).div (hpoly q) |>.sub (analyticAt_const.meromorphicAt)).div ((hpoly r).div (hpoly s))
  have he : (fun α : ℝ => (bc_hitGen Q z α i).toReal) =ᶠ[𝓝[<] 1] F := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from zero_lt_one)] with α hα
    have hgi : (bc_green Q α i z).toReal = p.eval α / q.eval α := by
      rw [bc_green_eq Q hQ]
      exact (hp α hα).2
    have hgz : (bc_green Q α z z).toReal = r.eval α / s.eval α := by
      rw [bc_green_eq Q hQ]
      exact (hr α hα).2
    have hg1 : (1 : ℝ) ≤ (bc_green Q α z z).toReal := by
      simpa using (ENNReal.toReal_le_toReal ENNReal.one_ne_top (bc_green_finite Q hQ hα z z)).mpr (bc_green_diagonal_ge_one Q z α)
    dsimp [F]
    rw [← hgi,← hgz]
    apply (eq_div_iff (ne_of_gt (lt_of_lt_of_le zero_lt_one hg1))).mpr
    have hi := bc_green_hit_real Q hQ z hα i
    linarith
  have hb : ∀ᶠ α : ℝ in 𝓝[<] 1, ‖F α‖ ≤ 1 := by
    filter_upwards [he,Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from zero_lt_one)] with α heα hα
    rw [← heα,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
    simpa using (ENNReal.toReal_le_toReal (bc_hitGen_finite Q hQ z hα i) ENNReal.one_ne_top).mpr (bc_hitGen_le_one Q hQ z hα i)
  obtain ⟨g,hg,hfg⟩ := bc_meromorphic_extension F hm 1 hb
  have heg := he.trans hfg
  have ht := (bc_hitGen_toReal_limit Q hQ z i).congr' heg
  have htg : Tendsto g (𝓝[<] 1) (𝓝 (g 1)) := hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact ⟨g,hg,heg,tendsto_nhds_unique htg ht⟩

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section

lemma bc_tail_series_finite (u : ℕ → ℝ≥0∞) (hu : (∑' n, u n) ≠ ⊤)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 1) : bc_series (bc_tail u) α ≠ ⊤ := by
  have hb := bc_renewal_balance u hα
  intro hd
  have ha : ENNReal.ofReal (1-α) ≠ 0 := (ENNReal.ofReal_pos.mpr (sub_pos.mpr hα.2)).ne'
  rw [hd,ENNReal.mul_top ha,add_top] at hb
  exact hu hb.symm

lemma bc_moment_finite_of_analytic (u : ℕ → ℝ≥0∞) (hu : (∑' n, u n) ≠ ⊤) (g : ℝ → ℝ)
    (hg : AnalyticAt ℝ g 1) (he : (fun α : ℝ => (bc_series u α).toReal) =ᶠ[𝓝[<] 1] g)
    (hval : g 1 = (∑' n, u n).toReal) : (∑' n : ℕ, (n : ℝ≥0∞) * u n) ≠ ⊤ := by
  have hs := hg.differentiableAt.hasDerivAt.tendsto_slope.mono_left (nhdsLT_le_nhdsNE (1 : ℝ))
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hs
  have heq : (fun α : ℝ => bc_series (bc_tail u) α) =ᶠ[𝓝[<] 1]
      (fun α => ENNReal.ofReal (slope g 1 α)) := by
    filter_upwards [he,Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from zero_lt_one)] with α heα hα
    have hD := bc_tail_series_finite u hu hα
    have hH : bc_series u α ≠ ⊤ := by
      apply ne_top_of_le_ne_top hu
      have hb := bc_renewal_balance u hα
      exact (le_add_right (le_refl (bc_series u α))).trans_eq hb
    have hb := congrArg ENNReal.toReal (bc_renewal_balance u hα)
    rw [ENNReal.toReal_add hH (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hD),ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hα.2.le),heα,← hval] at hb
    have hreal : (bc_series (bc_tail u) α).toReal = slope g 1 α := by
      rw [slope_def_field]
      apply (eq_div_iff (sub_ne_zero.mpr hα.2.ne)).mpr
      nlinarith
    rw [← hreal,ENNReal.ofReal_toReal hD]
  have hlim := ht.congr' heq.symm
  have htail := bc_series_left_limit (bc_tail u)
  rw [bc_tail_mass] at htail
  have hx := tendsto_nhds_unique htail hlim
  rw [hx]
  exact ENNReal.ofReal_ne_top

variable {S : Type*} [Fintype S]

lemma bc_hit_moment_finite (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z i : S) :
    (∑' n : ℕ, (n : ℝ≥0∞) * firstPassage Q {z} n i) ≠ ⊤ := by
  obtain ⟨g,hg,he,hval⟩ := bc_hitGen_analytic_extension Q hQ z i
  exact bc_moment_finite_of_analytic (fun n => firstPassage Q {z} n i)
    (ne_top_of_le_ne_top ENNReal.one_ne_top (bc_reachProb_le_one Q hQ z i)) g hg he hval

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S : Type*} [Fintype S]

lemma bc_class_reach_singleton (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    (hz : PositiveRecurrent Q z) (i : S) : reachProb Q (commClass Q z) i = reachProb Q {z} i := by
  have hc : ∀ j ∈ commClass Q z, ∀ k, Q j k ≠ 0 → k ∈ commClass Q z :=
    fun j hj k hjk => bc_class_closed Q hQ z hz hj hjk
  have hb : ∀ j ∈ commClass Q z, reachProb Q (commClass Q z) j = 1 :=
    bc_reach_set_closed_boundary Q hQ (commClass Q z) hc
  have hhit : ∀ j ∈ commClass Q z, reachProb Q {z} j = 1 :=
    fun j hj => bc_recurrent_reachable_hit_one Q hQ z hz.1 j hj.1
  apply le_antisymm
  · exact bc_reach_set_minimal Q (commClass Q z) (fun k => reachProb Q {z} k)
      (fun k => (bc_harmonic_set_boundary_rec Q (commClass Q z) _ (bc_recurrent_harmonic_enn Q hQ z hz.1) hhit k).le) i
  · exact bc_reach_minimal Q z (fun k => reachProb Q (commClass Q z) k)
      (fun k => (bc_harmonic_boundary_rec Q z _ (bc_reach_set_harmonic Q (commClass Q z) hb)
        (hb z ⟨bc_leads_refl Q z,bc_leads_refl Q z⟩) k).le) i

lemma bc_distinguished_class_mass (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (Z : Finset S)
    (hZ : IsDistinguishedSet Q Z) (i : S) : ∑ z ∈ Z, reachProb Q (commClass Q z) i = 1 := by
  calc
    _ = ∑ z ∈ Z, reachProb Q {z} i := by
      apply Finset.sum_congr rfl
      intro z hz
      exact bc_class_reach_singleton Q hQ z (hZ.1 z hz) i
    _ = 1 := bc_distinguished_mass Q hQ Z hZ i

lemma bc_meanPassage_finite_of_hit_one (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z i : S)
    (hi : reachProb Q {z} i = 1) : meanPassage Q z i ≠ ⊤ := by
  simp only [meanPassage,if_pos hi]
  exact bc_hit_moment_finite Q hQ z i

end
end SennottDP.AvgFinite

set_option maxHeartbeats 1000000

namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S : Type*} [Fintype S]

def bc_killENN (Q : S → S → ℝ≥0∞) (z : S) : Matrix S S ℝ≥0∞ := Matrix.of fun i j => if j=z then 0 else Q i j

lemma bc_taboo_pow (Q : S → S → ℝ≥0∞) (z : S) (n : ℕ) : Matrix.of (tabooStep Q z n) = (bc_killENN Q z)^n := by
  induction n with
  | zero => ext i j; simp [tabooStep,Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ,← ih]
    ext i j
    change (if j=z then 0 else ∑ k, tabooStep Q z n i k * Q k j) =
      ∑ k, tabooStep Q z n i k * (if j=z then 0 else Q k j)
    by_cases hj : j=z <;> simp [hj]

lemma bc_taboo_backward (Q : S → S → ℝ≥0∞) (z : S) (n : ℕ) (i j : S) :
    tabooStep Q z (n+1) i j = ∑ k, (if k=z then 0 else Q i k) * tabooStep Q z n k j := by
  change Matrix.of (tabooStep Q z (n+1)) i j = _
  rw [bc_taboo_pow,pow_succ',← bc_taboo_pow]
  rfl

lemma bc_taboo_le_nStep (Q : S → S → ℝ≥0∞) (z : S) (n : ℕ) (i j : S) : tabooStep Q z n i j ≤ nStep Q n i j := by
  induction n generalizing i j with
  | zero => simp [tabooStep,nStep]
  | succ n ih =>
    rw [bc_taboo_backward,bc_nStep_backward]
    apply Finset.sum_le_sum
    intro k _
    by_cases hk : k=z
    · simp [hk]
    · simp only [hk,if_false]
      exact mul_le_mul' le_rfl (ih k j)

lemma bc_firstPass_taboo (Q : S → S → ℝ≥0∞) (z : S) (n : ℕ) (i : S) :
    firstPassage Q {z} (n+1) i = ∑ j, tabooStep Q z n i j * Q j z := by
  induction n generalizing i with
  | zero => simp [firstPassage,tabooStep]
  | succ n ih =>
    rw [bc_firstPass_step]
    simp only [Nat.succ_ne_zero,if_false,zero_add]
    simp_rw [ih,bc_taboo_backward,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k=z
    · simp [hk]
    · simp only [hk,if_false,Finset.mul_sum,mul_assoc]

lemma bc_taboo_pass_comp (Q : S → S → ℝ≥0∞) (z : S) (s n : ℕ) (i : S) :
    (∑ j, tabooStep Q z s i j * firstPassage Q {z} (n+1) j) = firstPassage Q {z} (s+n+1) i := by
  induction s generalizing i with
  | zero => simp [tabooStep]
  | succ s ih =>
    simp_rw [bc_taboo_backward,Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc,← Finset.mul_sum,ih]
    rw [show s+1+n+1 = (s+n+1)+1 by omega,bc_firstPass_step]
    simp only [show s+n+1 ≠ 0 by omega,if_false,zero_add]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k=z <;> simp [hk]

lemma bc_tail_shift (u : ℕ → ℝ≥0∞) (s : ℕ) : bc_tail u s = ∑' n : ℕ, u (s+n+1) := by
  have hsum : Summable (fun n : ℕ => if s < n+(s+1) then u (n+(s+1)) else 0) := ENNReal.summable
  have ht := Summable.sum_add_tsum_nat_add' (f := fun n : ℕ => if s < n then u n else 0) (k := s+1) hsum
  have hz : (∑ n ∈ Finset.range (s+1), if s < n then u n else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hn' : n < s+1 := Finset.mem_range.mp hn
    exact if_neg (by omega : ¬ s < n)
  rw [hz,zero_add] at ht
  unfold bc_tail
  rw [← ht]
  apply tsum_congr
  intro n
  simp only [if_pos (by omega : s < n+(s+1))]
  congr 1
  omega

lemma bc_taboo_hit_tail (Q : S → S → ℝ≥0∞) (z : S) (s : ℕ) (i : S) :
    ∑ j, tabooStep Q z s i j * reachProb Q {z} j = bc_tail (fun n => firstPassage Q {z} n i) s := by
  have hr (j : S) : reachProb Q {z} j = ∑' n : ℕ, firstPassage Q {z} (n+1) j := by
    unfold reachProb
    rw [tsum_eq_zero_add' ENNReal.summable]
    have hz : firstPassage Q {z} 0 j = 0 := rfl
    rw [hz,zero_add]
  simp_rw [hr,← ENNReal.tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable),bc_tail_shift]
  apply tsum_congr
  intro n
  exact bc_taboo_pass_comp Q z s n i

lemma bc_onHitTime_eq_moment (Q : S → S → ℝ≥0∞) (z i : S) :
    onHitSum Q z (fun _ => 1) i = ∑' n : ℕ, (n : ℝ≥0∞) * firstPassage Q {z} n i := by
  simp only [onHitSum,mul_one]
  simp_rw [bc_taboo_hit_tail]
  exact bc_tail_mass _

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S Act : Type*} [Fintype S]

lemma bc_induced_sum (M : MDC S Act) (e : StationaryPolicy M) (i : S) : ∑ j, inducedChain M e i j = 1 := by
  simpa only [inducedChain,tsum_fintype] using M.P_sum i (e.f i)

lemma bc_expCost_chain (M : MDC S Act) (e : StationaryPolicy M) (n : ℕ) (i : S) :
    expCost e.toPolicy i n = ∑ j, nStep (inducedChain M e) n i j * (M.C j (e.f j) : ℝ≥0∞) := by
  induction n generalizing i with
  | zero => rw [bf_expCost_zero]; simp [nStep]
  | succ n ih =>
    rw [bf_expCost_succ,tsum_fintype]
    simp_rw [ih,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [bc_nStep_backward,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    change inducedChain M e i k * (nStep (inducedChain M e) n k j * _) = _
    ring

lemma bc_native_green_cost (M : MDC S Act) (e : StationaryPolicy M) (α : ℝ) (i : S) :
    discCost e.toPolicy α i = ∑ j, bc_green (inducedChain M e) α i j * (M.C j (e.f j) : ℝ≥0∞) := by
  unfold discCost bc_green
  simp_rw [bc_expCost_chain,Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro j _
  rw [← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro n
  ring

lemma bc_native_avg_projection (M : MDC S Act) (e : StationaryPolicy M) (i : S) :
    avgCost e.toPolicy i = ∑ j, bc_projection (inducedChain M e) (bc_induced_sum M e) i j * (M.C j (e.f j) : ℝ≥0∞) := by
  have ht := tendsto_finsetSum Finset.univ (fun j _ => ENNReal.Tendsto.mul_const (b := (M.C j (e.f j) : ℝ≥0∞))
    (bc_green_limit (inducedChain M e) (bc_induced_sum M e) i j) (Or.inr ENNReal.coe_ne_top))
  have he : (fun α : ℝ => ENNReal.ofReal (1-α) * discCost e.toPolicy α i) =
      (fun α => ∑ j, (ENNReal.ofReal (1-α) * bc_green (inducedChain M e) α i j) * (M.C j (e.f j) : ℝ≥0∞)) := by
    funext α
    rw [bc_native_green_cost,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hf := (bf_stationary_limits_result M e i).1
  rw [he] at hf
  exact tendsto_nhds_unique hf ht

lemma bc_native_avg_ne_top (M : MDC S Act) (e : StationaryPolicy M) (i : S) : avgCost e.toPolicy i ≠ ⊤ := by
  rw [bc_native_avg_projection]
  exact ENNReal.sum_ne_top.mpr (fun j _ => ENNReal.mul_ne_top
    (bc_projection_ne_top (inducedChain M e) (bc_induced_sum M e) i j) ENNReal.coe_ne_top)

lemma bc_native_avg_classes (M : MDC S Act) (e : StationaryPolicy M) (Z : Finset S)
    (hZ : IsDistinguishedSet (inducedChain M e) Z) (i : S) :
    avgCost e.toPolicy i = ∑ z ∈ Z, classReachProb M e z i * avgCost e.toPolicy z := by
  rw [bc_native_avg_projection]
  simp_rw [bc_projection_distinguished _ _ Z hZ i,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [classReachProb,bc_class_reach_singleton (inducedChain M e) (bc_induced_sum M e) z (hZ.1 z hz),bc_native_avg_projection,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S : Type*} [Fintype S]

lemma bc_onHit_le_time (Q : S → S → ℝ≥0∞) (z : S) (g : S → ℝ≥0∞) (B : ℝ≥0∞)
    (hg : ∀ j, g j ≤ B) (i : S) : onHitSum Q z g i ≤ B * onHitSum Q z (fun _ => 1) i := by
  unfold onHitSum
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro s
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  calc
    tabooStep Q z s i j * g j * reachProb Q {z} j ≤ tabooStep Q z s i j * B * reachProb Q {z} j :=
      mul_le_mul' (mul_le_mul' le_rfl (hg j)) le_rfl
    _ = B * (tabooStep Q z s i j * 1 * reachProb Q {z} j) := by ring

lemma bc_onHit_finite (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    (g : S → ℝ≥0∞) (hg : ∀ j, g j ≠ ⊤) (i : S) : onHitSum Q z g i ≠ ⊤ := by
  have htime : onHitSum Q z (fun _ => 1) i ≠ ⊤ := by
    rw [bc_onHitTime_eq_moment]
    exact bc_hit_moment_finite Q hQ z i
  apply ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.sum_ne_top.mpr (fun j _ => hg j)) htime)
  apply bc_onHit_le_time Q z g (∑ j, g j)
  intro j
  exact Finset.single_le_sum (f := g) (fun _ _ => bot_le) (Finset.mem_univ j)

lemma bc_onHit_rec (Q : S → S → ℝ≥0∞) (z : S) (g : S → ℝ≥0∞) (i : S) :
    onHitSum Q z g i = g i * reachProb Q {z} i + ∑ k, if k=z then 0 else Q i k * onHitSum Q z g k := by
  unfold onHitSum
  rw [tsum_eq_zero_add' ENNReal.summable]
  have hz : (∑ j, tabooStep Q z 0 i j * g j * reachProb Q {z} j) = g i * reachProb Q {z} i := by simp [tabooStep]
  rw [hz]
  have hs (n : ℕ) : (∑ j, tabooStep Q z (n+1) i j * g j * reachProb Q {z} j) =
      ∑ k, (if k=z then 0 else Q i k) * ∑ j, tabooStep Q z n k j * g j * reachProb Q {z} j := by
    simp_rw [bc_taboo_backward,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hs]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k=z
  · simp [hk]
  · simp only [hk,if_false,ENNReal.tsum_mul_left]

lemma bc_onHit_real_rec (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    (g : S → ℝ≥0∞) (hg : ∀ j, g j ≠ ⊤) (i : S) :
    (onHitSum Q z g i).toReal = (g i).toReal * (reachProb Q {z} i).toReal +
      ∑ k, bc_kill Q z i k * (onHitSum Q z g k).toReal := by
  have hv k : (if k=z then 0 else Q i k * onHitSum Q z g k) ≠ ⊤ := by
    split_ifs
    · finiteness
    · exact ENNReal.mul_ne_top (bc_Q_ne_top Q hQ i k) (bc_onHit_finite Q hQ z g hg k)
  have he := congrArg ENNReal.toReal (bc_onHit_rec Q z g i)
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (hg i)
    (ne_top_of_le_ne_top ENNReal.one_ne_top (bc_reachProb_le_one Q hQ z i)))
    (ENNReal.sum_ne_top.mpr (fun k _ => hv k)),ENNReal.toReal_mul,ENNReal.toReal_sum (fun k _ => hv k)] at he
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k=z <;> simp [hk,bc_kill,ENNReal.toReal_mul]

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S : Type*} [Fintype S]

def bc_tabooGreen (Q : S → S → ℝ≥0∞) (z : S) (α : ℝ) (i j : S) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal α ^ n * tabooStep Q z n i j

lemma bc_tabooGreen_le_green (Q : S → S → ℝ≥0∞) (z : S) (α : ℝ) (i j : S) :
    bc_tabooGreen Q z α i j ≤ bc_green Q α i j :=
  ENNReal.tsum_le_tsum (fun n => mul_le_mul' le_rfl (bc_taboo_le_nStep Q z n i j))

lemma bc_tabooGreen_finite (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 1) (i j : S) : bc_tabooGreen Q z α i j ≠ ⊤ :=
  ne_top_of_le_ne_top (bc_green_finite Q hQ hα i j) (bc_tabooGreen_le_green Q z α i j)

lemma bc_tabooGreen_rec (Q : S → S → ℝ≥0∞) (z : S) (α : ℝ) (i j : S) :
    bc_tabooGreen Q z α i j = (if i=j then 1 else 0) +
      ENNReal.ofReal α * ∑ k, if k=z then 0 else Q i k * bc_tabooGreen Q z α k j := by
  unfold bc_tabooGreen
  rw [tsum_eq_zero_add' ENNReal.summable]
  have hz : tabooStep Q z 0 i j = (if i=j then 1 else 0) := rfl
  simp only [pow_zero,hz,one_mul]
  congr 1
  simp_rw [bc_taboo_backward,pow_succ,Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k=z
  · simp [hk]
  · simp only [hk,if_false]
    rw [← ENNReal.tsum_mul_left,← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro n
    ring

lemma bc_tabooGreen_real_rec (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z j : S)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    (fun i => (bc_tabooGreen Q z α i j).toReal) = (fun i => if i=j then 1 else 0) +
      α • (bc_kill Q z).mulVec (fun i => (bc_tabooGreen Q z α i j).toReal) := by
  funext i
  have hv k : (if k=z then 0 else Q i k * bc_tabooGreen Q z α k j) ≠ ⊤ := by
    split_ifs
    · finiteness
    · exact ENNReal.mul_ne_top (bc_Q_ne_top Q hQ i k) (bc_tabooGreen_finite Q hQ z hα k j)
  have hd : (if i=j then (1 : ℝ≥0∞) else 0) ≠ ⊤ := by split_ifs <;> finiteness
  have he := congrArg ENNReal.toReal (bc_tabooGreen_rec Q z α i j)
  rw [ENNReal.toReal_add hd (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.sum_ne_top.mpr (fun k _ => hv k))),
    ENNReal.toReal_mul,ENNReal.toReal_ofReal hα.1.le,ENNReal.toReal_sum (fun k _ => hv k)] at he
  change (bc_tabooGreen Q z α i j).toReal = (if i=j then 1 else 0) +
    α * ∑ k, bc_kill Q z i k * (bc_tabooGreen Q z α k j).toReal
  rw [he]
  have hdR : (if i=j then (1 : ℝ≥0∞) else 0).toReal = (if i=j then 1 else 0) := by split_ifs <;> simp
  rw [hdR]
  congr 2
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k=z <;> simp [hk,bc_kill,ENNReal.toReal_mul]

lemma bc_green_taboo_real (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z j : S)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 1) (i : S) :
    (bc_green Q α i j).toReal = (bc_tabooGreen Q z α i j).toReal +
      (bc_hitGen Q z α i).toReal * (bc_green Q α z j).toReal := by
  let g : S → ℝ := fun k => (bc_green Q α k j).toReal
  let t : S → ℝ := fun k => (bc_tabooGreen Q z α k j).toReal
  let h : S → ℝ := fun k => (bc_hitGen Q z α k).toReal
  let d : S → ℝ := fun k => if k=j then 1 else 0
  let q : S → ℝ := fun k => (Q k z).toReal
  let K := bc_kill Q z
  have hg : g = (d + α • ((g z) • q)) + α • K.mulVec g := by
    have he := bc_green_real_rec Q hQ j hα
    change g = d + α • (bf_P (bc_model Q hQ (fun _ => 0)) (bc_policy Q hQ _)).mulVec g at he
    conv_lhs => rw [he]
    rw [bc_split_column Q hQ z g,smul_add]
    abel
  have hu : t + (g z) • h = (d + α • ((g z) • q)) + α • K.mulVec (t + (g z) • h) := by
    have ht : t = d + α • K.mulVec t := bc_tabooGreen_real_rec Q hQ z j hα
    have hh : h = α • q + α • K.mulVec h := bc_hitGen_real_rec Q hQ z hα
    conv_lhs => rw [ht,hh]
    rw [smul_add,Matrix.mulVec_add,Matrix.mulVec_smul,smul_add]
    simp only [smul_comm (g z) α]
    abel
  have he := bc_substoch_unique K (bc_kill_nonneg Q z) (bc_kill_sum Q hQ z) α hα
    (d + α • ((g z) • q)) g (t+(g z)•h) hg hu
  have hi := congrFun he i
  change g i = t i + h i * g z
  change g i = t i + g z * h i at hi
  nlinarith

lemma bc_green_taboo (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z j : S)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 1) (i : S) :
    bc_green Q α i j = bc_tabooGreen Q z α i j + bc_hitGen Q z α i * bc_green Q α z j := by
  have hf := ENNReal.mul_ne_top (bc_hitGen_finite Q hQ z hα i) (bc_green_finite Q hQ hα z j)
  apply (ENNReal.toReal_eq_toReal_iff' (bc_green_finite Q hQ hα i j)
    (ENNReal.add_ne_top.mpr ⟨bc_tabooGreen_finite Q hQ z hα i j,hf⟩)).mp
  rw [ENNReal.toReal_add (bc_tabooGreen_finite Q hQ z hα i j) hf,ENNReal.toReal_mul]
  exact bc_green_taboo_real Q hQ z j hα i

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S Act : Type*} [Fintype S]

lemma bc_return_weight (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    (hz : reachProb Q {z} z = 1) (n : ℕ) (j : S) :
    tabooStep Q z n z j * reachProb Q {z} j = tabooStep Q z n z j := by
  by_cases ht : tabooStep Q z n z j = 0
  · simp [ht]
  · have hn : nStep Q n z j ≠ 0 := by
      intro he
      exact ht (le_antisymm ((bc_taboo_le_nStep Q z n z j).trans_eq he) bot_le)
    rw [bc_recurrent_reachable_hit_one Q hQ z hz j ⟨n,hn⟩,mul_one]

lemma bc_onHit_return_unweighted (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    (hz : reachProb Q {z} z = 1) (g : S → ℝ≥0∞) :
    onHitSum Q z g z = ∑' n : ℕ, ∑ j, tabooStep Q z n z j * g j := by
  unfold onHitSum
  apply tsum_congr
  intro n
  apply Finset.sum_congr rfl
  intro j _
  calc
    tabooStep Q z n z j * g j * reachProb Q {z} j = (tabooStep Q z n z j * reachProb Q {z} j) * g j := by ring
    _ = tabooStep Q z n z j * g j := by rw [bc_return_weight Q hQ z hz]

def bc_tabooCost (M : MDC S Act) (e : StationaryPolicy M) (z : S) (α : ℝ) (i : S) : ℝ≥0∞ :=
  bc_series (fun n => ∑ j, tabooStep (inducedChain M e) z n i j * (M.C j (e.f j) : ℝ≥0∞)) α

lemma bc_tabooCost_green (M : MDC S Act) (e : StationaryPolicy M) (z : S) (α : ℝ) (i : S) :
    bc_tabooCost M e z α i = ∑ j, bc_tabooGreen (inducedChain M e) z α i j * (M.C j (e.f j) : ℝ≥0∞) := by
  unfold bc_tabooCost bc_series bc_tabooGreen
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro j _
  rw [← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro n
  ring

lemma bc_native_cost_taboo (M : MDC S Act) (e : StationaryPolicy M) (z : S)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 1) (i : S) :
    discCost e.toPolicy α i = bc_tabooCost M e z α i +
      bc_hitGen (inducedChain M e) z α i * discCost e.toPolicy α z := by
  rw [bc_native_green_cost M e α i,bc_tabooCost_green,bc_native_green_cost M e α z]
  simp_rw [bc_green_taboo (inducedChain M e) (bc_induced_sum M e) z _ hα i,add_mul]
  rw [Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma bc_tabooCost_finite (M : MDC S Act) (e : StationaryPolicy M) (z : S)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 1) (i : S) : bc_tabooCost M e z α i ≠ ⊤ := by
  apply ne_top_of_le_ne_top (bf_disc_finite M e.toPolicy hα i)
  rw [bc_native_cost_taboo M e z hα i]
  exact le_self_add

lemma bc_tabooCost_return_limit (M : MDC S Act) (e : StationaryPolicy M) (z : S)
    (hz : reachProb (inducedChain M e) {z} z = 1) :
    Tendsto (fun α : ℝ => bc_tabooCost M e z α z) (𝓝[<] 1) (𝓝 (condPassCost M e z z)) := by
  have ht := bc_series_left_limit (fun n => ∑ j, tabooStep (inducedChain M e) z n z j * (M.C j (e.f j) : ℝ≥0∞))
  rw [← bc_onHit_return_unweighted (inducedChain M e) (bc_induced_sum M e) z hz] at ht
  exact ht

lemma bc_return_discount_balance (M : MDC S Act) (e : StationaryPolicy M) (z : S)
    (hz : reachProb (inducedChain M e) {z} z = 1) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    bc_tabooCost M e z α z = (ENNReal.ofReal (1-α) * discCost e.toPolicy α z) *
      bc_series (bc_tail (fun n => firstPassage (inducedChain M e) {z} n z)) α := by
  let Q := inducedChain M e
  let H := bc_hitGen Q z α z
  let D := bc_series (bc_tail (fun n => firstPassage Q {z} n z)) α
  let V := discCost e.toPolicy α z
  let T := bc_tabooCost M e z α z
  have hH : H ≠ ⊤ := bc_hitGen_finite Q (bc_induced_sum M e) z hα z
  have hD : D ≠ ⊤ := bc_tail_series_finite _ (by change reachProb Q {z} z ≠ ⊤; rw [hz]; exact ENNReal.one_ne_top) hα
  have hV : V ≠ ⊤ := bf_disc_finite M e.toPolicy hα z
  have hT : T ≠ ⊤ := bc_tabooCost_finite M e z hα z
  have hb := bc_renewal_balance (fun n => firstPassage Q {z} n z) hα
  change H + ENNReal.ofReal (1-α) * D = reachProb Q {z} z at hb
  rw [hz] at hb
  have hbR := congrArg ENNReal.toReal hb
  rw [ENNReal.toReal_add hH (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hD),ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hα.2.le),ENNReal.toReal_one] at hbR
  have hc : V = T + H * V := bc_native_cost_taboo M e z hα z
  have hcR := congrArg ENNReal.toReal hc
  rw [ENNReal.toReal_add hT (ENNReal.mul_ne_top hH hV),ENNReal.toReal_mul] at hcR
  apply (ENNReal.toReal_eq_toReal_iff' hT (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV) hD)).mp
  rw [ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal (sub_nonneg.mpr hα.2.le)]
  have he := congrArg (fun x : ℝ => x * V.toReal) hbR
  nlinarith

lemma bc_return_cost_identity (M : MDC S Act) (e : StationaryPolicy M) (z : S)
    (hz : PositiveRecurrent (inducedChain M e) z) :
    condPassCost M e z z = avgCost e.toPolicy z * condPassTime M e z z := by
  have hd := bc_series_left_limit (bc_tail (fun n => firstPassage (inducedChain M e) {z} n z))
  rw [bc_tail_mass,← bc_onHitTime_eq_moment] at hd
  have hdF : condPassTime M e z z ≠ ⊤ := bc_onHit_finite (inducedChain M e) (bc_induced_sum M e) z (fun _ => 1) (fun _ => ENNReal.one_ne_top) z
  have hp := ENNReal.Tendsto.mul (bf_stationary_limits_result M e z).1 (Or.inr hdF) hd (Or.inr (bc_native_avg_ne_top M e z))
  have he : (fun α : ℝ => bc_tabooCost M e z α z) =ᶠ[𝓝[<] 1] (fun α =>
      (ENNReal.ofReal (1-α) * discCost e.toPolicy α z) * bc_series (bc_tail (fun n => firstPassage (inducedChain M e) {z} n z)) α) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from zero_lt_one)] with α hα
    exact bc_return_discount_balance M e z hz.1 hα
  exact tendsto_nhds_unique (bc_tabooCost_return_limit M e z hz.1) (hp.congr' he.symm)

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Topology
open Classical Filter
noncomputable section
variable {S Act : Type*} [Fintype S]

def bf_policyEquiv (M : MDC S Act) : StationaryPolicy M ≃ (∀ i, {a : Act // a ∈ M.A i}) where
  toFun e i := ⟨e.f i,e.mem i⟩
  invFun g := ⟨fun i => (g i).1,fun i => (g i).2⟩
  left_inv e := by cases e; rfl
  right_inv g := by funext i; rfl

instance bf_stationaryFintype (M : MDC S Act) : Fintype (StationaryPolicy M) := by
  letI : ∀ i : S, Fintype {a : Act // a ∈ M.A i} := fun i => Fintype.ofFinset (M.A i) (fun _ => Iff.rfl)
  exact Fintype.ofEquiv (∀ i, {a : Act // a ∈ M.A i}) (bf_policyEquiv M).symm

lemma bf_ratio_sign_near (p q : Polynomial ℝ) :
    (∀ᶠ α : ℝ in 𝓝[<] 1, p.eval α / q.eval α = 0) ∨
    (∀ᶠ α : ℝ in 𝓝[<] 1, 0 < p.eval α / q.eval α) ∨
    (∀ᶠ α : ℝ in 𝓝[<] 1, p.eval α / q.eval α < 0) := by
  rcases bf_polynomial_sign_near p with hp | hp | hp
  · left
    exact Eventually.of_forall (fun α => by rw [hp α,zero_div])
  · rcases bf_polynomial_sign_near q with hq | hq | hq
    · left
      exact Eventually.of_forall (fun α => by rw [hq α,div_zero])
    · right;left
      filter_upwards [hp,hq] with α hα hqα
      exact div_pos hα hqα
    · right;right
      filter_upwards [hp,hq] with α hα hqα
      exact div_neg_of_pos_of_neg hα hqα
  · rcases bf_polynomial_sign_near q with hq | hq | hq
    · left
      exact Eventually.of_forall (fun α => by rw [hq α,div_zero])
    · right;right
      filter_upwards [hp,hq] with α hα hqα
      exact div_neg_of_neg_of_pos hα hqα
    · right;left
      filter_upwards [hp,hq] with α hα hqα
      exact div_pos_of_neg_of_neg hα hqα

lemma bf_comparison_stable (M : MDC S Act) (f g : StationaryPolicy M) (i : S) :
    ∃ b : Prop, ∀ᶠ α : ℝ in 𝓝[<] 1, (bf_v M f α i ≤ bf_v M g α i) ↔ b := by
  obtain ⟨p,q,hf⟩ := bf_rational_data M f i
  obtain ⟨r,s,hg⟩ := bf_rational_data M g i
  let num := p*s-r*q
  let den := q*s
  have he (α : ℝ) (hα : α ∈ Set.Ioo 0 1) :
      num.eval α / den.eval α = bf_v M f α i - bf_v M g α i := by
    rw [(hf α hα).2,(hg α hα).2]
    simp only [num,den,Polynomial.eval_sub,Polynomial.eval_mul]
    field_simp [(hf α hα).1,(hg α hα).1]
    <;> ring
  have hI : ∀ᶠ α : ℝ in 𝓝[<] 1, α ∈ Set.Ioo 0 1 := Ioo_mem_nhdsLT zero_lt_one
  rcases bf_ratio_sign_near num den with hz | hp | hn
  · refine ⟨True,?_⟩
    filter_upwards [hz,hI] with α hα hIα
    rw [he α hIα] at hα
    exact iff_true_intro (sub_eq_zero.mp hα).le
  · refine ⟨False,?_⟩
    filter_upwards [hp,hI] with α hα hIα
    rw [he α hIα] at hα
    exact iff_false_intro (not_le.mpr (sub_pos.mp hα))
  · refine ⟨True,?_⟩
    filter_upwards [hn,hI] with α hα hIα
    rw [he α hIα] at hα
    exact iff_true_intro (sub_neg.mp hα).le

lemma bf_blackwell_exists (M : MDC S Act) :
    ∃ α₀ ∈ Set.Ioo (0 : ℝ) 1, ∃ f : StationaryPolicy M,
      ∀ α ∈ Set.Ioo α₀ 1, IsDiscountOptimal f.toPolicy α := by
  choose b hb using bf_comparison_stable M
  have hall : ∀ᶠ α : ℝ in 𝓝[<] 1, ∀ (f g : StationaryPolicy M) (i : S),
      (bf_v M f α i ≤ bf_v M g α i) ↔ b f g i := by
    exact eventually_all.mpr (fun f => eventually_all.mpr (fun g => eventually_all.mpr (fun i => hb f g i)))
  obtain ⟨l,hl,hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hall
  let α₀ := max l (1/2 : ℝ)
  have hα₀ : α₀ ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    · exact max_lt hl (by norm_num)
  let αbar : ℝ := (α₀+1)/2
  have hbar : αbar ∈ Set.Ioo α₀ 1 := by dsimp [αbar]; constructor <;> linarith [hα₀.2]
  let abar : ℝ≥0 := ⟨αbar,lt_trans hα₀.1 hbar.1 |>.le⟩
  obtain ⟨f,hf⟩ := bf_discount_optimal_exists M abar
  refine ⟨α₀,hα₀,f,fun α hα i => ?_⟩
  have hα' : α ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_trans hα₀.1 hα.1,hα.2⟩
  let a : ℝ≥0 := ⟨α,hα'.1.le⟩
  obtain ⟨g,hg⟩ := bf_discount_optimal_exists M a
  have hbarall := hsub (show αbar ∈ Set.Ioo l 1 from ⟨lt_of_le_of_lt (le_max_left _ _) hbar.1,hbar.2⟩)
  have hαall := hsub (show α ∈ Set.Ioo l 1 from ⟨lt_of_le_of_lt (le_max_left _ _) hα.1,hα.2⟩)
  have hbarle : bf_v M f αbar i ≤ bf_v M g αbar i := by
    have hv : discCost f.toPolicy αbar i = discValue M αbar i := hf i
    apply (ENNReal.toReal_le_toReal (bf_disc_finite M f.toPolicy ⟨(lt_trans hα₀.1 hbar.1),hbar.2⟩ i)
      (bf_disc_finite M g.toPolicy ⟨(lt_trans hα₀.1 hbar.1),hbar.2⟩ i)).mpr
    rw [hv]
    exact iInf_le _ g.toPolicy
  have hle : bf_v M f α i ≤ bf_v M g α i := (hαall f g i).mpr ((hbarall f g i).mp hbarle)
  have hle' : discCost f.toPolicy α i ≤ discCost g.toPolicy α i :=
    (ENNReal.toReal_le_toReal (bf_disc_finite M f.toPolicy hα' i) (bf_disc_finite M g.toPolicy hα' i)).mp hle
  apply le_antisymm
  · exact hle'.trans_eq (hg i)
  · exact iInf_le _ f.toPolicy

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Topology
open Classical Filter
noncomputable section
variable {S Act : Type*} [Fintype S]

lemma bf_blackwell_average (M : MDC S Act) (f : StationaryPolicy M) (α₀ : ℝ)
    (hα₀ : α₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hf : ∀ α ∈ Set.Ioo α₀ 1, IsDiscountOptimal f.toPolicy α) :
    IsAverageOptimal f.toPolicy := by
  intro i
  have hmin (θ : Policy M) : avgCost f.toPolicy i ≤ avgCost θ i := by
    have ht := (bf_stationary_limits_result M f i).1
    have he : (fun α : ℝ => ENNReal.ofReal (1-α) * discCost f.toPolicy α i)
        ≤ᶠ[𝓝[<] 1] (fun α : ℝ => ENNReal.ofReal (1-α) * discCost θ α i) := by
      filter_upwards [Ioo_mem_nhdsLT hα₀.2] with α hα
      rw [hf α hα i]
      exact mul_le_mul_right (iInf_le _ θ) _
    have hle := limsup_le_limsup he
    rw [ht.limsup_eq] at hle
    exact hle.trans (bf_abel_result M θ i).2.2.1
  exact le_antisymm (le_iInf hmin) (iInf_le _ f.toPolicy)

lemma bf_blackwell_result (M : MDC S Act) :
    ∃ α₀ ∈ Set.Ioo (0 : ℝ) 1, ∃ f : StationaryPolicy M,
      (∀ α ∈ Set.Ioo α₀ 1, IsDiscountOptimal f.toPolicy α) ∧
      IsAverageOptimal f.toPolicy ∧
      ∀ i : S,
        Tendsto (fun α : ℝ => ENNReal.ofReal (1-α) * discValue M α i) (𝓝[<] 1)
          (𝓝 (avgValue M i)) ∧
        Tendsto (fun n : ℕ => horizonCost f.toPolicy n i / (n : ℝ≥0∞)) atTop
          (𝓝 (avgValue M i)) := by
  obtain ⟨α₀,hα₀,f,hf⟩ := bf_blackwell_exists M
  have ha := bf_blackwell_average M f α₀ hα₀ hf
  refine ⟨α₀,hα₀,f,hf,ha,fun i => ?_⟩
  obtain ⟨ht,hc⟩ := bf_stationary_limits_result M f i
  rw [ha i] at ht hc
  refine ⟨?_,hc⟩
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsLT hα₀.2] with α hα
  rw [hf α hα i]

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S Act : Type*} [Fintype S]

lemma bc_onHit_zero (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    (g : S → ℝ≥0∞) (hg : ∀ j, g j ≠ ⊤) (i : S) (hi : reachProb Q {z} i = 0) : onHitSum Q z g i = 0 := by
  have hf : ∀ n, firstPassage Q {z} n i = 0 := fun n =>
    le_antisymm ((ENNReal.le_tsum n).trans_eq hi) bot_le
  have ht : onHitSum Q z (fun _ => 1) i = 0 := by rw [bc_onHitTime_eq_moment]; simp [hf]
  have hl := bc_onHit_le_time Q z g (∑ j, g j) (fun j => Finset.single_le_sum (f := g) (fun _ _ => bot_le) (Finset.mem_univ j)) i
  rw [ht,mul_zero] at hl
  exact le_antisymm hl bot_le

lemma bc_condCost_finite (M : MDC S Act) (f : StationaryPolicy M) (z i : S) : condPassCost M f z i ≠ ⊤ :=
  bc_onHit_finite (inducedChain M f) (bc_induced_sum M f) z _ (fun _ => ENNReal.coe_ne_top) i

lemma bc_condTime_finite (M : MDC S Act) (f : StationaryPolicy M) (z i : S) : condPassTime M f z i ≠ ⊤ :=
  bc_onHit_finite (inducedChain M f) (bc_induced_sum M f) z _ (fun _ => ENNReal.one_ne_top) i

def bc_passBias (M : MDC S Act) (f : StationaryPolicy M) (z i : S) : ℝ :=
  (condPassCost M f z i).toReal - (avgCost f.toPolicy z).toReal * (condPassTime M f z i).toReal

lemma bc_passBias_return_zero (M : MDC S Act) (f : StationaryPolicy M) (z : S)
    (hz : PositiveRecurrent (inducedChain M f) z) : bc_passBias M f z z = 0 := by
  unfold bc_passBias
  rw [bc_return_cost_identity M f z hz,ENNReal.toReal_mul,sub_self]

lemma bc_passBias_kill_rec (M : MDC S Act) (f : StationaryPolicy M) (z i : S) :
    bc_passBias M f z i = ((M.C i (f.f i) : ℝ) - (avgCost f.toPolicy z).toReal) *
      (reachProb (inducedChain M f) {z} i).toReal +
      ∑ k, bc_kill (inducedChain M f) z i k * bc_passBias M f z k := by
  have hc := bc_onHit_real_rec (inducedChain M f) (bc_induced_sum M f) z
    (fun j => (M.C j (f.f j) : ℝ≥0∞)) (fun _ => ENNReal.coe_ne_top) i
  have ht := bc_onHit_real_rec (inducedChain M f) (bc_induced_sum M f) z
    (fun _ => 1) (fun _ => ENNReal.one_ne_top) i
  simp only [ENNReal.coe_toReal,ENNReal.toReal_one,one_mul] at hc ht
  unfold bc_passBias condPassCost condPassTime
  rw [hc,ht]
  simp only [bc_kill,Matrix.of_apply]
  simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.mul_sum]
  have he : (∑ k, (avgCost f.toPolicy z).toReal *
      ((if k=z then 0 else (inducedChain M f i k).toReal) * (onHitSum (inducedChain M f) z (fun _ => 1) k).toReal)) =
      ∑ k, (if k=z then 0 else (inducedChain M f i k).toReal) *
        ((avgCost f.toPolicy z).toReal * (onHitSum (inducedChain M f) z (fun _ => 1) k).toReal) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  ring

lemma bc_passBias_rec (M : MDC S Act) (f : StationaryPolicy M) (z : S)
    (hz : PositiveRecurrent (inducedChain M f) z) (i : S) :
    bc_passBias M f z i = ((M.C i (f.f i) : ℝ) - (avgCost f.toPolicy z).toReal) *
      (reachProb (inducedChain M f) {z} i).toReal +
      ∑ k, (M.P i (f.f i) k).toReal * bc_passBias M f z k := by
  have he := bc_split_column (inducedChain M f) (bc_induced_sum M f) z (bc_passBias M f z)
  rw [bc_passBias_return_zero M f z hz,zero_smul,zero_add] at he
  have hi := congrFun he i
  change (∑ k, (M.P i (f.f i) k).toReal * bc_passBias M f z k) =
    (∑ k, bc_kill (inducedChain M f) z i k * bc_passBias M f z k) at hi
  rw [bc_passBias_kill_rec M f z i,← hi]

lemma bc_passBias_zero_of_hit_zero (M : MDC S Act) (f : StationaryPolicy M) (z i : S)
    (hi : reachProb (inducedChain M f) {z} i = 0) : bc_passBias M f z i = 0 := by
  unfold bc_passBias condPassCost condPassTime
  rw [bc_onHit_zero (inducedChain M f) (bc_induced_sum M f) z _ (fun _ => ENNReal.coe_ne_top) i hi,
    bc_onHit_zero (inducedChain M f) (bc_induced_sum M f) z _ (fun _ => ENNReal.one_ne_top) i hi]
  simp

lemma bc_bias_distinguished_zero (M : MDC S Act) (f : StationaryPolicy M) (Z : Finset S)
    (hZ : IsDistinguishedSet (inducedChain M f) Z) (z : S) (hz : z ∈ Z) : relValue M f Z z = 0 := by
  change (∑ k ∈ Z, bc_passBias M f k z) = 0
  apply Finset.sum_eq_zero
  intro k hk
  by_cases h : k=z
  · subst k; exact bc_passBias_return_zero M f z (hZ.1 z hz)
  · exact bc_passBias_zero_of_hit_zero M f k z (bc_distinguished_reach_zero _ (bc_induced_sum M f) Z hZ hk hz h)

lemma bc_avg_classes_real (M : MDC S Act) (f : StationaryPolicy M) (Z : Finset S)
    (hZ : IsDistinguishedSet (inducedChain M f) Z) (i : S) :
    (avgCost f.toPolicy i).toReal = ∑ z ∈ Z, (reachProb (inducedChain M f) {z} i).toReal * (avgCost f.toPolicy z).toReal := by
  rw [bc_native_avg_classes M f Z hZ i]
  have hF (z : S) (_hz : z ∈ Z) : classReachProb M f z i * avgCost f.toPolicy z ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ne_top_of_le_ne_top ENNReal.one_ne_top
        (bc_reach_set_le_one (inducedChain M f) (bc_induced_sum M f) (commClass (inducedChain M f) z) i)
    · exact bc_native_avg_ne_top M f z
  rw [ENNReal.toReal_sum hF]
  apply Finset.sum_congr rfl
  intro z hz
  rw [ENNReal.toReal_mul,classReachProb,bc_class_reach_singleton (inducedChain M f) (bc_induced_sum M f) z (hZ.1 z hz)]

lemma bc_bias_poisson (M : MDC S Act) (f : StationaryPolicy M) (Z : Finset S)
    (hZ : IsDistinguishedSet (inducedChain M f) Z) (i : S) :
    (avgCost f.toPolicy i).toReal + relValue M f Z i = (M.C i (f.f i) : ℝ) +
      ∑ k, (M.P i (f.f i) k).toReal * relValue M f Z k := by
  have hm := congrArg ENNReal.toReal (bc_distinguished_mass (inducedChain M f) (bc_induced_sum M f) Z hZ i)
  rw [ENNReal.toReal_sum (fun z _ => ne_top_of_le_ne_top ENNReal.one_ne_top (bc_reachProb_le_one _ (bc_induced_sum M f) z i)),ENNReal.toReal_one] at hm
  change (avgCost f.toPolicy i).toReal + (∑ z ∈ Z, bc_passBias M f z i) =
    (M.C i (f.f i) : ℝ) + ∑ k, (M.P i (f.f i) k).toReal * ∑ z ∈ Z, bc_passBias M f z k
  have hs : (∑ z ∈ Z, bc_passBias M f z i) =
      (∑ z ∈ Z, ((M.C i (f.f i) : ℝ) - (avgCost f.toPolicy z).toReal) * (reachProb (inducedChain M f) {z} i).toReal) +
      ∑ k, (M.P i (f.f i) k).toReal * ∑ z ∈ Z, bc_passBias M f z k := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    exact bc_passBias_rec M f z (hZ.1 z hz) i
  rw [hs]
  simp_rw [sub_mul,Finset.sum_sub_distrib]
  rw [← Finset.mul_sum,hm,mul_one,bc_avg_classes_real M f Z hZ i]
  have he : (∑ z ∈ Z, (avgCost f.toPolicy z).toReal * (reachProb (inducedChain M f) {z} i).toReal) =
      ∑ z ∈ Z, (reachProb (inducedChain M f) {z} i).toReal * (avgCost f.toPolicy z).toReal := by
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [he]
  ring

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S Act : Type*} [Fintype S]

lemma bc_gain_harmonic (M : MDC S Act) (f : StationaryPolicy M) (Z : Finset S)
    (hZ : IsDistinguishedSet (inducedChain M f) Z) (i : S) :
    ∑ k, (M.P i (f.f i) k).toReal * (avgCost f.toPolicy k).toReal = (avgCost f.toPolicy i).toReal := by
  calc
    _ = ∑ k, (M.P i (f.f i) k).toReal *
        (∑ z ∈ Z, (reachProb (inducedChain M f) {z} k).toReal * (avgCost f.toPolicy z).toReal) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [bc_avg_classes_real M f Z hZ k]
    _ = ∑ z ∈ Z, (reachProb (inducedChain M f) {z} i).toReal * (avgCost f.toPolicy z).toReal := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z hz
      simp_rw [← mul_assoc,← Finset.sum_mul]
      have he := congrFun (bc_recurrent_harmonic (inducedChain M f) (bc_induced_sum M f) z (hZ.1 z hz).1) i
      change (∑ k, (M.P i (f.f i) k).toReal * (reachProb (inducedChain M f) {z} k).toReal) = _ at he
      rw [he]
    _ = _ := (bc_avg_classes_real M f Z hZ i).symm

def bc_resolvent (Q : S → S → ℝ≥0∞) (α : ℝ) (w : S → ℝ) (i : S) : ℝ :=
  ∑ j, (bc_green Q α i j).toReal * w j

lemma bc_resolvent_rec (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 1) (w : S → ℝ) (i : S) :
    bc_resolvent Q α w i = w i + α * ∑ k, (Q i k).toReal * bc_resolvent Q α w k := by
  unfold bc_resolvent
  have he (j : S) : (bc_green Q α i j).toReal = (if i=j then 1 else 0) +
      α * ∑ k, (Q i k).toReal * (bc_green Q α k j).toReal := congrFun (bc_green_real_rec Q hQ j hα) i
  simp_rw [he,add_mul,Finset.sum_add_distrib]
  have hd : (∑ j, (if i=j then (1 : ℝ) else 0) * w j) = w i := by simp
  rw [hd]
  congr 1
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma bc_scaled_green_real_limit (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (i j : S) :
    Tendsto (fun α : ℝ => (1-α) * (bc_green Q α i j).toReal) (𝓝[<] 1) (𝓝 (bc_projection Q hQ i j).toReal) := by
  have ht := (ENNReal.tendsto_toReal (bc_projection_ne_top Q hQ i j)).comp (bc_green_limit Q hQ i j)
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from zero_lt_one)] with α hα
  change (ENNReal.ofReal (1-α) * bc_green Q α i j).toReal = _
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (sub_nonneg.mpr hα.2.le)]

lemma bc_resolvent_scaled_limit (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (w : S → ℝ) (i : S) :
    Tendsto (fun α : ℝ => (1-α) * bc_resolvent Q α w i) (𝓝[<] 1)
      (𝓝 (∑ j, (bc_projection Q hQ i j).toReal * w j)) := by
  have ht := tendsto_finsetSum Finset.univ (fun j _ => (bc_scaled_green_real_limit Q hQ i j).mul (tendsto_const_nhds (x := w j)))
  convert ht using 1
  funext α
  simp only [bc_resolvent,Finset.mul_sum,mul_assoc]

lemma bc_native_value_rec_real (M : MDC S Act) (f : StationaryPolicy M) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    bf_v M f α = bf_c M f + α • (bf_P M f).mulVec (bf_v M f α) := by
  have he := bf_v_equation M f hα
  rw [bf_A,Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec] at he
  exact sub_eq_iff_eq_add.mp he

lemma bc_discount_bias_formula (M : MDC S Act) (f : StationaryPolicy M) (g w : S → ℝ)
    (hg : ∀ i, ∑ k, (M.P i (f.f i) k).toReal * g k = g i)
    (hw : ∀ i, g i + w i = (M.C i (f.f i) : ℝ) + ∑ k, (M.P i (f.f i) k).toReal * w k)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 1) (i : S) :
    (discCost f.toPolicy α i).toReal = g i / (1-α) + (w i -
      (1-α) * bc_resolvent (inducedChain M f) α w i) / α := by
  let R : S → ℝ := bc_resolvent (inducedChain M f) α w
  let v : S → ℝ := fun k => g k / (1-α) + (w k - (1-α) * R k) / α
  have hv : v = bf_c M f + α • (bf_P M f).mulVec v := by
    funext k
    change g k / (1-α) + (w k - (1-α) * R k) / α = (M.C k (f.f k) : ℝ) +
      α * ∑ j, (M.P k (f.f k) j).toReal * (g j / (1-α) + (w j - (1-α) * R j) / α)
    have hsum : (∑ j, (M.P k (f.f k) j).toReal * (g j / (1-α) + (w j - (1-α) * R j) / α)) =
        g k / (1-α) + ((∑ j, (M.P k (f.f k) j).toReal * w j) -
          (1-α)*(∑ j, (M.P k (f.f k) j).toReal * R j)) / α := by
      simp only [mul_add,mul_sub,← mul_div_assoc,Finset.sum_add_distrib,← Finset.sum_div,
        Finset.sum_sub_distrib]
      rw [hg k]
      congr 2
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum]
    have hr := bc_resolvent_rec (inducedChain M f) (bc_induced_sum M f) hα w k
    change R k = w k + α * ∑ j, (M.P k (f.f k) j).toReal * R j at hr
    have hd : g k / (1-α) = g k + α * (g k / (1-α)) := by
      field_simp [ne_of_gt (sub_pos.mpr hα.2)]
      ring
    have hnum : (w k - (1-α)*R k) / α = w k - (1-α)*(∑ j, (M.P k (f.f k) j).toReal * R j) := by
      apply (div_eq_iff hα.1.ne').mpr
      have hm := congrArg (fun x : ℝ => (1-α)*x) hr
      nlinarith
    rw [hnum,mul_add,mul_div_cancel₀ _ hα.1.ne']
    nlinarith [hw k]
  have he := bc_substoch_unique (bf_P M f) (bf_P_nonneg M f) (fun k => (bf_P_sum M f k).le) α hα
    (bf_c M f) (bf_v M f α) v (bc_native_value_rec_real M f hα) hv
  exact congrFun he i

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S Act : Type*} [Fintype S]

lemma bc_projection_distinguished_real (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (Z : Finset S)
    (hZ : IsDistinguishedSet Q Z) (i j : S) :
    (bc_projection Q hQ i j).toReal = ∑ z ∈ Z, (reachProb Q {z} i).toReal * (bc_projection Q hQ z j).toReal := by
  rw [bc_projection_distinguished Q hQ Z hZ i j,ENNReal.toReal_sum (fun z _ => ENNReal.mul_ne_top
    (ne_top_of_le_ne_top ENNReal.one_ne_top (bc_reachProb_le_one Q hQ z i)) (bc_projection_ne_top Q hQ z j))]
  simp only [ENNReal.toReal_mul]

lemma bc_projection_action_decomp (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (Z : Finset S)
    (hZ : IsDistinguishedSet Q Z) (w : S → ℝ) (i : S) :
    (∑ j, (bc_projection Q hQ i j).toReal * w j) =
      ∑ z ∈ Z, (reachProb Q {z} i).toReal * ∑ j, (bc_projection Q hQ z j).toReal * w j := by
  simp_rw [bc_projection_distinguished_real Q hQ Z hZ i,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma bc_biasNorm_eq_projection (M : MDC S Act) (f : StationaryPolicy M) (Z : Finset S)
    (hZ : IsDistinguishedSet (inducedChain M f) Z) (i : S) :
    relValueNorm M f Z i = relValue M f Z i -
      ∑ j, (bc_projection (inducedChain M f) (bc_induced_sum M f) i j).toReal * relValue M f Z j := by
  rw [bc_projection_action_decomp (inducedChain M f) (bc_induced_sum M f) Z hZ]
  unfold relValueNorm
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  rw [classReachProb,bc_class_reach_singleton (inducedChain M f) (bc_induced_sum M f) z (hZ.1 z hz)]
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  rw [bc_projection_class_row _ _ z (hZ.1 z hz)]
  by_cases hj : j ∈ commClass (inducedChain M f) z <;> simp [hj]

lemma bc_bias_limit (M : MDC S Act) (f : StationaryPolicy M) (Z : Finset S)
    (hZ : IsDistinguishedSet (inducedChain M f) Z) (i : S) :
    Tendsto (fun α : ℝ => (discCost f.toPolicy α i).toReal - (avgCost f.toPolicy i).toReal / (1-α))
      (𝓝[<] 1) (𝓝 (relValueNorm M f Z i)) := by
  have ht := (tendsto_const_nhds (x := relValue M f Z i)).sub
    (bc_resolvent_scaled_limit (inducedChain M f) (bc_induced_sum M f) (relValue M f Z) i)
  have hα : Tendsto (fun α : ℝ => α) (𝓝[<] 1) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hd := ht.div hα one_ne_zero
  simp only [div_one] at hd
  rw [← bc_biasNorm_eq_projection M f Z hZ i] at hd
  apply hd.congr'
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from zero_lt_one)] with α hα
  change (relValue M f Z i - (1-α) * bc_resolvent (inducedChain M f) α (relValue M f Z) i) / α =
    (discCost f.toPolicy α i).toReal - (avgCost f.toPolicy i).toReal / (1-α)
  rw [bc_discount_bias_formula M f (fun k => (avgCost f.toPolicy k).toReal) (relValue M f Z)
    (bc_gain_harmonic M f Z hZ) (bc_bias_poisson M f Z hZ) hα i]
  ring

lemma bc_laurent_result (M : MDC S Act) (f : StationaryPolicy M) (α₀ : ℝ)
    (hα₀ : α₀ ∈ Set.Ioo 0 1) (hf : ∀ α ∈ Set.Ioo α₀ 1, IsDiscountOptimal f.toPolicy α)
    (Z : Finset S) (hZ : IsDistinguishedSet (inducedChain M f) Z) (i : S) :
    Tendsto (fun α : ℝ => (discValue M α i).toReal - (avgValue M i).toReal / (1-α) - relValueNorm M f Z i)
      (𝓝[<] 1) (𝓝 0) := by
  have ha := bf_blackwell_average M f α₀ hα₀ hf
  have ht := (bc_bias_limit M f Z hZ i).sub (tendsto_const_nhds (x := relValueNorm M f Z i))
  rw [sub_self,ha i] at ht
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsLT hα₀.2] with α hα
  rw [hf α hα i]

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S Act : Type*} [Fintype S]

lemma bc_classReach_ne_top (M : MDC S Act) (f : StationaryPolicy M) (z i : S) : classReachProb M f z i ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (bc_reach_set_le_one _ (bc_induced_sum M f) _ i)

lemma bc_Wdisc_real (M : MDC S Act) (f : StationaryPolicy M) (Z : Finset S) {α : ℝ}
    (hα : α ∈ Set.Ioo 0 1) (i : S) : (Wdisc M f Z α i).toReal =
      ∑ z ∈ Z, (classReachProb M f z i).toReal * (discValue M α z).toReal := by
  unfold Wdisc
  rw [ENNReal.toReal_sum (fun z _ => ENNReal.mul_ne_top (bc_classReach_ne_top M f z i)
    (ne_top_of_le_ne_top (bf_disc_finite M f.toPolicy hα z) (iInf_le _ f.toPolicy)))]
  simp only [ENNReal.toReal_mul]

lemma bc_discountValue_scale_limit (M : MDC S Act) (f : StationaryPolicy M) (α₀ : ℝ)
    (hα₀ : α₀ ∈ Set.Ioo 0 1) (hf : ∀ α ∈ Set.Ioo α₀ 1, IsDiscountOptimal f.toPolicy α) (i : S) :
    Tendsto (fun α : ℝ => ENNReal.ofReal (1-α) * discValue M α i) (𝓝[<] 1) (𝓝 (avgCost f.toPolicy i)) := by
  apply (bf_stationary_limits_result M f i).1.congr'
  filter_upwards [Ioo_mem_nhdsLT hα₀.2] with α hα
  rw [hf α hα i]

lemma bc_Wdisc_limit (M : MDC S Act) (f : StationaryPolicy M) (α₀ : ℝ)
    (hα₀ : α₀ ∈ Set.Ioo 0 1) (hf : ∀ α ∈ Set.Ioo α₀ 1, IsDiscountOptimal f.toPolicy α)
    (Z : Finset S) (hZ : IsDistinguishedSet (inducedChain M f) Z) (i : S) :
    Tendsto (fun α : ℝ => ENNReal.ofReal (1-α) * Wdisc M f Z α i) (𝓝[<] 1) (𝓝 (avgValue M i)) := by
  have ht := tendsto_finsetSum Z (fun z _ => ENNReal.Tendsto.mul
    (tendsto_const_nhds (x := classReachProb M f z i)) (Or.inr (bc_native_avg_ne_top M f z))
    (bc_discountValue_scale_limit M f α₀ hα₀ hf z) (Or.inr (bc_classReach_ne_top M f z i)))
  rw [← bc_native_avg_classes M f Z hZ i,(bf_blackwell_average M f α₀ hα₀ hf) i] at ht
  convert ht using 1
  funext α
  rw [Wdisc,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

lemma bc_wdisc_limit (M : MDC S Act) (f : StationaryPolicy M) (α₀ : ℝ)
    (hα₀ : α₀ ∈ Set.Ioo 0 1) (hf : ∀ α ∈ Set.Ioo α₀ 1, IsDiscountOptimal f.toPolicy α)
    (Z : Finset S) (hZ : IsDistinguishedSet (inducedChain M f) Z) (i : S) :
    Tendsto (fun α : ℝ => wdisc M f Z α i) (𝓝[<] 1) (𝓝 (relValue M f Z i)) := by
  let Q := inducedChain M f
  let hQ := bc_induced_sum M f
  let w := relValue M f Z
  let d : ℝ → S → ℝ := fun α k => (discCost f.toPolicy α k).toReal - (avgCost f.toPolicy k).toReal / (1-α)
  have hs : (∑ z ∈ Z, (reachProb Q {z} i).toReal * relValueNorm M f Z z) =
      -(∑ j, (bc_projection Q hQ i j).toReal * w j) := by
    calc
      _ = ∑ z ∈ Z, -( (reachProb Q {z} i).toReal * ∑ j, (bc_projection Q hQ z j).toReal * w j) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [bc_biasNorm_eq_projection M f Z hZ z,bc_bias_distinguished_zero M f Z hZ z hz]
        ring
      _ = -(∑ z ∈ Z, (reachProb Q {z} i).toReal * ∑ j, (bc_projection Q hQ z j).toReal * w j) := by rw [Finset.sum_neg_distrib]
      _ = _ := by rw [bc_projection_action_decomp Q hQ Z hZ w i]
  have hval : relValueNorm M f Z i - (∑ z ∈ Z, (reachProb Q {z} i).toReal * relValueNorm M f Z z) = w i := by
    rw [hs,bc_biasNorm_eq_projection M f Z hZ i]
    ring
  have ht := (bc_bias_limit M f Z hZ i).sub (tendsto_finsetSum Z (fun z _ =>
    (tendsto_const_nhds (x := (reachProb Q {z} i).toReal)).mul (bc_bias_limit M f Z hZ z)))
  rw [hval] at ht
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsLT hα₀.2] with α hα
  have hα01 : α ∈ Set.Ioo (0 : ℝ) 1 := ⟨hα₀.1.trans hα.1,hα.2⟩
  unfold wdisc
  rw [bc_Wdisc_real M f Z hα01 i]
  have hopt (j : S) : discValue M α j = discCost f.toPolicy α j := (hf α hα j).symm
  simp_rw [hopt]
  have hr (z : S) (hz : z ∈ Z) : classReachProb M f z i = reachProb Q {z} i :=
    bc_class_reach_singleton Q hQ z (hZ.1 z hz) i
  have hsum : (∑ z ∈ Z, (classReachProb M f z i).toReal * (discCost f.toPolicy α z).toReal) =
      (∑ z ∈ Z, (reachProb Q {z} i).toReal * (discCost f.toPolicy α z).toReal) := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [hr z hz]
  rw [hsum]
  have hd : (∑ z ∈ Z, (reachProb Q {z} i).toReal * d α z) =
      (∑ z ∈ Z, (reachProb Q {z} i).toReal * (discCost f.toPolicy α z).toReal) -
        (avgCost f.toPolicy i).toReal / (1-α) := by
    dsimp [d]
    simp only [mul_sub,← mul_div_assoc,Finset.sum_sub_distrib,← Finset.sum_div]
    rw [← bc_avg_classes_real M f Z hZ i]
  change d α i - (∑ z ∈ Z, (reachProb Q {z} i).toReal * d α z) = _
  rw [hd]
  dsimp [d]
  ring

lemma bc_expected_bias_vanish (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (w : S → ℝ) (i : S) :
    Tendsto (fun n : ℕ => (∑ j, (nStep Q n i j).toReal * w j) / (n : ℝ)) atTop (𝓝 0) := by
  let B : ℝ := ∑ j, ‖w j‖
  have hb (n : ℕ) : ‖∑ j, (nStep Q n i j).toReal * w j‖ ≤ B := by
    calc
      _ ≤ ∑ j, ‖(nStep Q n i j).toReal * w j‖ := norm_sum_le _ _
      _ ≤ B := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
        have hp : (nStep Q n i j).toReal ≤ 1 := by
          simpa using (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (bc_nStep_le_one Q hQ n i j)) ENNReal.one_ne_top).mpr (bc_nStep_le_one Q hQ n i j)
        simpa using mul_le_mul_of_nonneg_right hp (norm_nonneg (w j))
  have hn : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ht := (tendsto_const_nhds (x := B)).mul hn
  simp only [mul_zero] at ht
  apply squeeze_zero_norm (fun n => ?_) ht
  simp only [div_eq_mul_inv,norm_mul,Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹)]
  simpa only [Real.norm_eq_abs] using mul_le_mul_of_nonneg_right (hb n) (by positivity : 0 ≤ (n : ℝ)⁻¹)

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
open SennottDP.BlackwellFH
noncomputable section
variable {S Act : Type*} [Fintype S]

lemma bc_value_action_le (M : MDC S Act) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) (i : S) (a : Act) (ha : a ∈ M.A i) :
    discValue M α i ≤ (M.C i a : ℝ≥0∞) + ENNReal.ofReal α * ∑ k, M.P i a k * discValue M α k := by
  let β : ℝ≥0 := ⟨α,hα.1.le⟩
  have hv := bf_value_eq_limit M β
  have he : bf_limit M β i ≤ fa_Q (bf_model M) β (bf_limit M β) i a := by
    rw [bf_limit_fixed M β i]
    exact Finset.inf'_le _ ha
  rw [← hv] at he
  have hβ : (β : ℝ) = α := rfl
  have hβE : (β : ℝ≥0∞) = ENNReal.ofReal α := by rw [← ENNReal.ofReal_coe_nnreal,hβ]
  simpa only [fa_Q,bf_model,tsum_fintype,hβ,hβE] using he

lemma bc_normalized_native_real_limit (M : MDC S Act) (f : StationaryPolicy M) (i : S) :
    Tendsto (fun α : ℝ => (1-α) * (discCost f.toPolicy α i).toReal) (𝓝[<] 1) (𝓝 (avgCost f.toPolicy i).toReal) := by
  have ht := (ENNReal.tendsto_toReal (bc_native_avg_ne_top M f i)).comp (bf_stationary_limits_result M f i).1
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from zero_lt_one)] with α hα
  change (ENNReal.ofReal (1-α) * discCost f.toPolicy α i).toReal = _
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (sub_nonneg.mpr hα.2.le)]

lemma bc_gain_inequality (M : MDC S Act) (f : StationaryPolicy M) (α₀ : ℝ)
    (hα₀ : α₀ ∈ Set.Ioo 0 1) (hf : ∀ α ∈ Set.Ioo α₀ 1, IsDiscountOptimal f.toPolicy α)
    (e : StationaryPolicy M) (i : S) :
    (avgCost f.toPolicy i).toReal ≤ ∑ k, (M.P i (e.f i) k).toReal * (avgCost f.toPolicy k).toReal := by
  have hα : Tendsto (fun α : ℝ => α) (𝓝[<] 1) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
  have ha : Tendsto (fun α : ℝ => 1-α) (𝓝[<] 1) (𝓝 0) := by simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hα
  have hc := ha.mul (tendsto_const_nhds (x := (M.C i (e.f i) : ℝ)))
  have hs := tendsto_finsetSum Finset.univ (fun k _ => (tendsto_const_nhds (x := (M.P i (e.f i) k).toReal)).mul (bc_normalized_native_real_limit M f k))
  have hr := hc.add (hα.mul hs)
  simp only [zero_mul,one_mul,zero_add] at hr
  apply le_of_tendsto_of_tendsto (bc_normalized_native_real_limit M f i) hr
  filter_upwards [Ioo_mem_nhdsLT hα₀.2] with α hα'
  have hα01 : α ∈ Set.Ioo (0 : ℝ) 1 := ⟨hα₀.1.trans hα'.1,hα'.2⟩
  have he := bc_value_action_le M hα01 i (e.f i) (e.mem i)
  have hopt (j : S) : discValue M α j = discCost f.toPolicy α j := (hf α hα' j).symm
  simp_rw [hopt] at he
  have hP (k : S) : M.P i (e.f i) k ≠ ⊤ := bc_Q_ne_top (inducedChain M e) (bc_induced_sum M e) i k
  have hV (k : S) : discCost f.toPolicy α k ≠ ⊤ := bf_disc_finite M f.toPolicy hα01 k
  have hS : (∑ k, M.P i (e.f i) k * discCost f.toPolicy α k) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun k _ => ENNReal.mul_ne_top (hP k) (hV k))
  have hfinite : ((M.C i (e.f i) : ℝ≥0∞) + ENNReal.ofReal α * ∑ k, M.P i (e.f i) k * discCost f.toPolicy α k) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top,ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS⟩
  have heR := (ENNReal.toReal_le_toReal (hV i) hfinite).mpr he
  rw [ENNReal.toReal_add ENNReal.coe_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS),
    ENNReal.toReal_mul,ENNReal.toReal_ofReal hα01.1.le,
    ENNReal.toReal_sum (fun k _ => ENNReal.mul_ne_top (hP k) (hV k))] at heR
  simp only [ENNReal.toReal_mul,ENNReal.coe_toReal] at heR
  have hscaled := mul_le_mul_of_nonneg_left heR (sub_nonneg.mpr hα'.2.le)
  convert hscaled using 1
  rw [mul_add]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S : Type*} [Fintype S]

lemma bc_projection_real_invariant (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (i j : S) :
    ∑ k, (bc_projection Q hQ i k).toReal * (Q k j).toReal = (bc_projection Q hQ i j).toReal := by
  have he := congrArg ENNReal.toReal (bc_projection_invariant Q hQ i j)
  rw [ENNReal.toReal_sum (fun k _ => ENNReal.mul_ne_top (bc_projection_ne_top Q hQ i k) (bc_Q_ne_top Q hQ k j))] at he
  simpa only [ENNReal.toReal_mul] using he

lemma bc_projection_real_class_pos (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    (hz : PositiveRecurrent Q z) (j : S) (hj : j ∈ commClass Q z) : 0 < (bc_projection Q hQ z j).toReal := by
  have hjp := bc_reachable_positive Q hQ z hz j hj.1
  have hne : bc_projection Q hQ z j ≠ 0 := by
    rw [bc_projection_class_row Q hQ z hz j,if_pos hj,← bc_projection_steady Q hQ j]
    exact (bc_positive_iff_projection Q hQ j).mp hjp
  exact ENNReal.toReal_pos hne (bc_projection_ne_top Q hQ z j)

lemma bc_subharmonic_class_harmonic (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    (hz : PositiveRecurrent Q z) (g : S → ℝ) (hg : ∀ i, g i ≤ ∑ k, (Q i k).toReal * g k)
    (j : S) (hj : j ∈ commClass Q z) : ∑ k, (Q j k).toReal * g k = g j := by
  let p : S → ℝ := fun k => (bc_projection Q hQ z k).toReal
  let d : S → ℝ := fun k => (∑ l, (Q k l).toReal * g l) - g k
  have hd : ∀ k, 0 ≤ d k := fun k => sub_nonneg.mpr (hg k)
  have hs : ∑ k, p k * d k = 0 := by
    dsimp [d]
    simp only [mul_sub,Finset.sum_sub_distrib]
    have he : (∑ k, p k * ∑ l, (Q k l).toReal * g l) = ∑ l, p l * g l := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      simp_rw [← mul_assoc,← Finset.sum_mul]
      rw [bc_projection_real_invariant Q hQ z l]
    rw [he,sub_self]
  have hl : p j * d j ≤ 0 := by
    rw [← hs]
    exact Finset.single_le_sum (f := fun k => p k * d k)
      (fun k _ => mul_nonneg ENNReal.toReal_nonneg (hd k)) (Finset.mem_univ j)
  have hp : 0 < p j := bc_projection_real_class_pos Q hQ z hz j hj
  have hzero : d j = 0 := by nlinarith [hd j]
  exact sub_eq_zero.mp hzero

lemma bc_nStep_real_harmonic_class (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    (hz : PositiveRecurrent Q z) (g : S → ℝ)
    (hg : ∀ j ∈ commClass Q z, ∑ k, (Q j k).toReal * g k = g j) (n : ℕ) (j : S) (hj : j ∈ commClass Q z) :
    ∑ k, (nStep Q n j k).toReal * g k = g j := by
  induction n generalizing j with
  | zero =>
    have he k : (if j=k then (1 : ℝ≥0∞) else 0).toReal * g k = if j=k then g k else 0 := by
      by_cases h : j=k <;> simp [h]
    simp_rw [nStep,he]
    simp
  | succ n ih =>
    simp_rw [bc_nStep_backward,ENNReal.toReal_sum (fun k _ => ENNReal.mul_ne_top (bc_Q_ne_top Q hQ j k)
      (ne_top_of_le_ne_top ENNReal.one_ne_top (bc_nStep_le_one Q hQ n k _))),ENNReal.toReal_mul,Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc,← Finset.mul_sum]
    calc
      _ = ∑ k, (Q j k).toReal * g k := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hQjk : Q j k = 0
        · simp [hQjk]
        · rw [ih k (bc_class_closed Q hQ z hz hj hQjk)]
      _ = g j := hg j hj

lemma bc_weighted_average_max (p v : S → ℝ) (hp : ∀ j, 0 ≤ p j) (hrow : ∑ j, p j = 1)
    (m : ℝ) (hv : ∀ j, p j ≠ 0 → v j ≤ m) (he : ∑ j, p j * v j = m) (j : S) (hj : p j ≠ 0) : v j = m := by
  have hnn k : 0 ≤ p k * (m-v k) := by
    by_cases hk : p k = 0
    · simp [hk]
    · exact mul_nonneg (hp k) (sub_nonneg.mpr (hv k hk))
  have hs : ∑ k, p k * (m-v k) = 0 := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul]
    rw [hrow,one_mul,he,sub_self]
  have hl : p j * (m-v j) ≤ 0 := by
    rw [← hs]
    exact Finset.single_le_sum (f := fun k => p k * (m-v k)) (fun k _ => hnn k) (Finset.mem_univ j)
  have hzero := le_antisymm hl (hnn j)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hj) |>.symm

lemma bc_subharmonic_class_constant (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (z : S)
    (hz : PositiveRecurrent Q z) (g : S → ℝ) (hg : ∀ i, g i ≤ ∑ k, (Q i k).toReal * g k)
    (j : S) (hj : j ∈ commClass Q z) : g j = g z := by
  let F := Finset.univ.filter (fun k => k ∈ commClass Q z)
  have hF : F.Nonempty := ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ z,⟨bc_leads_refl Q z,bc_leads_refl Q z⟩⟩⟩
  obtain ⟨m,hm,hmax⟩ := Finset.exists_max_image F g hF
  have hmclass : m ∈ commClass Q z := (Finset.mem_filter.mp hm).2
  have hhar : ∀ k ∈ commClass Q z, ∑ l, (Q k l).toReal * g l = g k :=
    fun k hk => bc_subharmonic_class_harmonic Q hQ z hz g hg k hk
  have hall (k : S) (hk : k ∈ commClass Q z) : g k = g m := by
    have hlead : LeadsTo Q m k := bc_leads_trans Q hmclass.2 hk.1
    obtain ⟨n,hn⟩ := hlead
    have he := bc_nStep_real_harmonic_class Q hQ z hz g hhar n m hmclass
    have hv : ∀ l, (nStep Q n m l).toReal ≠ 0 → g l ≤ g m := by
      intro l hl
      have hn' : nStep Q n m l ≠ 0 := fun h => hl (by simp [h])
      have hlclass := bc_recurrent_reachable_communicates Q hQ z hz.1 l (bc_leads_trans Q hmclass.1 ⟨n,hn'⟩)
      exact hmax l (by simp [F,hlclass])
    exact bc_weighted_average_max (fun l => (nStep Q n m l).toReal) g (fun _ => ENNReal.toReal_nonneg)
      (bc_nStep_real_sum Q hQ n m) (g m) hv he k
      (ENNReal.toReal_ne_zero.mpr ⟨hn,ne_top_of_le_ne_top ENNReal.one_ne_top (bc_nStep_le_one Q hQ n m k)⟩)

  exact (hall j hj).trans (hall z ⟨bc_leads_refl Q z,bc_leads_refl Q z⟩).symm

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite
open scoped ENNReal NNReal Matrix
open Classical Filter Topology
noncomputable section
variable {S Act : Type*} [Fintype S]

lemma bc_projection_real_action_invariant (Q : S → S → ℝ≥0∞) (hQ : ∀ i, ∑ j, Q i j = 1) (i : S) (w : S → ℝ) :
    (∑ j, (bc_projection Q hQ i j).toReal * ∑ k, (Q j k).toReal * w k) =
      ∑ k, (bc_projection Q hQ i k).toReal * w k := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [← mul_assoc,← Finset.sum_mul]
  rw [bc_projection_real_invariant Q hQ i k]

lemma bc_avg_projection_real (M : MDC S Act) (e : StationaryPolicy M) (i : S) :
    (avgCost e.toPolicy i).toReal = ∑ j,
      (bc_projection (inducedChain M e) (bc_induced_sum M e) i j).toReal * (M.C j (e.f j) : ℝ) := by
  rw [bc_native_avg_projection,ENNReal.toReal_sum (fun j _ => ENNReal.mul_ne_top
    (bc_projection_ne_top (inducedChain M e) (bc_induced_sum M e) i j) ENNReal.coe_ne_top)]
  simp only [ENNReal.toReal_mul,ENNReal.coe_toReal]

lemma bc_recurrent_verification (M : MDC S Act) (e : StationaryPolicy M) (g w : S → ℝ)
    (hsub : ∀ j, g j ≤ ∑ k, (M.P j (e.f j) k).toReal * g k)
    (hineq : ∀ j, (M.C j (e.f j) : ℝ) + ∑ k, (M.P j (e.f j) k).toReal * w k ≤ g j + w j)
    (i : S) (hi : PositiveRecurrent (inducedChain M e) i)
    (hlower : g i ≤ (avgCost e.toPolicy i).toReal) :
    g i + w i = (M.C i (e.f i) : ℝ) + ∑ k, (M.P i (e.f i) k).toReal * w k ∧
      (avgCost e.toPolicy i).toReal = g i := by
  let Q := inducedChain M e
  let hQ := bc_induced_sum M e
  let p : S → ℝ := fun j => (bc_projection Q hQ i j).toReal
  have hgain : ∑ j, p j * g j = g i := by
    have he : (∑ j, p j * g j) = (∑ j, p j * g i) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∈ commClass Q i
      · rw [bc_subharmonic_class_constant Q hQ i hi g hsub j hj]
      · have hpj : p j = 0 := by simp [p,bc_projection_class_row Q hQ i hi j,hj]
        simp [hpj]
    rw [he,← Finset.sum_mul]
    have hp : ∑ j, p j = 1 := by
      have he := congrArg ENNReal.toReal (bc_projection_row Q hQ i)
      rw [ENNReal.toReal_sum (fun j _ => bc_projection_ne_top Q hQ i j)] at he
      simpa using he
    rw [hp,one_mul]
  have hwInv : (∑ j, p j * ∑ k, (M.P j (e.f j) k).toReal * w k) = ∑ k, p k * w k :=
    bc_projection_real_action_invariant Q hQ i w
  have hcost : ∑ j, p j * (M.C j (e.f j) : ℝ) = (avgCost e.toPolicy i).toReal := (bc_avg_projection_real M e i).symm
  have hle : (avgCost e.toPolicy i).toReal ≤ g i := by
    have he := Finset.sum_le_sum (s := Finset.univ) (fun j _ => mul_le_mul_of_nonneg_left (hineq j) (show 0 ≤ p j from ENNReal.toReal_nonneg))
    simp only [mul_add,Finset.sum_add_distrib] at he
    rw [hcost,hwInv,hgain] at he
    linarith
  have havg := le_antisymm hle hlower
  let d : S → ℝ := fun j => g j + w j - ((M.C j (e.f j) : ℝ) + ∑ k, (M.P j (e.f j) k).toReal * w k)
  have hd : ∀ j, 0 ≤ d j := fun j => sub_nonneg.mpr (hineq j)
  have hs : ∑ j, p j * d j = 0 := by
    dsimp [d]
    simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]
    rw [hgain,hcost,hwInv,havg]
    ring
  have hl : p i * d i ≤ 0 := by
    rw [← hs]
    exact Finset.single_le_sum (f := fun j => p j * d j)
      (fun j _ => mul_nonneg ENNReal.toReal_nonneg (hd j)) (Finset.mem_univ i)
  have hp : 0 < p i := bc_projection_real_class_pos Q hQ i hi i ⟨bc_leads_refl Q i,bc_leads_refl Q i⟩
  have hdi : d i = 0 := by nlinarith [hd i]
  exact ⟨sub_eq_zero.mp hdi,havg⟩

end
end SennottDP.AvgFinite


namespace SennottDP.AvgFinite

open scoped ENNReal NNReal Topology
open Filter

/-- Theorem 6.3.1 (Sennott, pp. 101–102). Let `S` be finite, let `f` and `α₀ ∈ (0,1)` be as in
Proposition 6.2.3 (`f` is `α` discount optimal for every `α ∈ (α₀,1)`), and let `Z` contain one
distinguished state `z_k` from each positive recurrent class `R_k` of the chain induced by `f`.
With `W_α`, `w_α` as defined on p. 101, for every `i ∈ S`:
(i) `J(i) = lim_{α→1⁻} (1−α)W_α(i)`;
(ii) `lim_{α→1⁻} w_α(i) =: w(i) = ∑_k p_k(i)[c_{i|k}(f) − J_k m_{i|k}(f)]`;
(iii) `lim_{n→∞} E_f[w(X_n) | X_0 = i]/n = 0`;
(iv) the average cost optimality equation
`J(i) + w(i) = C(i,f) + ∑_j P_{ij}(f) w(j) ≥ min_a {C(i,a) + ∑_j P_{ij}(a) w(j)}` (6.6) holds;
(v) if `e` is a stationary policy realizing the minimum in (6.6) and the chain induced by `e` is
positive recurrent at `i`, then (6.6) is an equality at `i` and `J_e(i) = J(i)`. -/
theorem bc_acoe_result {S : Type*} {Act : Type*} [Fintype S] (M : MDC S Act)
    (f : StationaryPolicy M) (α₀ : ℝ) (hα₀ : α₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hf : ∀ α ∈ Set.Ioo α₀ 1, IsDiscountOptimal f.toPolicy α)
    (Z : Finset S) (hZ : IsDistinguishedSet (inducedChain M f) Z) (i : S) :
    let w : S → ℝ := relValue M f Z
    let rhs : S → Act → ℝ := fun j a => (M.C j a : ℝ) + ∑ k, (M.P j a k).toReal * w k
    let minRhs : S → ℝ := fun j => (M.A j).inf' (M.A_nonempty j) (rhs j)
    -- (i)
    Tendsto (fun α : ℝ => ENNReal.ofReal (1 - α) * Wdisc M f Z α i) (𝓝[<] 1)
        (𝓝 (avgValue M i)) ∧
    -- (ii)
    Tendsto (fun α : ℝ => wdisc M f Z α i) (𝓝[<] 1) (𝓝 (w i)) ∧
    -- (iii)
    Tendsto (fun n : ℕ => (∑ j, (nStep (inducedChain M f) n i j).toReal * w j) / (n : ℝ))
        atTop (𝓝 0) ∧
    -- (iv)
    ((avgValue M i).toReal + w i = rhs i (f.f i) ∧ rhs i (f.f i) ≥ minRhs i) ∧
    -- (v)
    (∀ e : StationaryPolicy M, (∀ j, rhs j (e.f j) = minRhs j) →
      PositiveRecurrent (inducedChain M e) i →
      (avgValue M i).toReal + w i = minRhs i ∧ avgCost e.toPolicy i = avgValue M i) := by
  dsimp only
  have ha := bf_blackwell_average M f α₀ hα₀ hf
  refine ⟨bc_Wdisc_limit M f α₀ hα₀ hf Z hZ i,
    bc_wdisc_limit M f α₀ hα₀ hf Z hZ i,
    bc_expected_bias_vanish (inducedChain M f) (bc_induced_sum M f) (relValue M f Z) i,
    ⟨?_,?_⟩,?_⟩
  · have he := bc_bias_poisson M f Z hZ i
    rw [ha i] at he
    exact he
  · exact Finset.inf'_le _ (f.mem i)
  · intro e he hi
    have hsub := bc_gain_inequality M f α₀ hα₀ hf e
    have hineq (j : S) : (M.C j (e.f j) : ℝ) + ∑ k, (M.P j (e.f j) k).toReal * relValue M f Z k ≤
        (avgCost f.toPolicy j).toReal + relValue M f Z j := by
      rw [he j]
      exact (Finset.inf'_le _ (f.mem j)).trans_eq (bc_bias_poisson M f Z hZ j).symm
    have hlower : (avgCost f.toPolicy i).toReal ≤ (avgCost e.toPolicy i).toReal := by
      apply (ENNReal.toReal_le_toReal (bc_native_avg_ne_top M f i) (bc_native_avg_ne_top M e i)).mpr
      rw [ha i]
      exact iInf_le _ e.toPolicy
    obtain ⟨hmin,havg⟩ := bc_recurrent_verification M e (fun j => (avgCost f.toPolicy j).toReal)
      (relValue M f Z) hsub hineq i hi hlower
    constructor
    · rw [← ha i,hmin,he i]
    · rw [← ha i]
      exact (ENNReal.toReal_eq_toReal_iff' (bc_native_avg_ne_top M e i) (bc_native_avg_ne_top M f i)).mp havg


end SennottDP.AvgFinite

open SennottDP.AvgFinite

open scoped ENNReal NNReal Topology
open Filter

/-- Theorem 6.3.1 (Sennott, pp. 101–102). Let `S` be finite, let `f` and `α₀ ∈ (0,1)` be as in
Proposition 6.2.3 (`f` is `α` discount optimal for every `α ∈ (α₀,1)`), and let `Z` contain one
distinguished state `z_k` from each positive recurrent class `R_k` of the chain induced by `f`.
With `W_α`, `w_α` as defined on p. 101, for every `i ∈ S`:
(i) `J(i) = lim_{α→1⁻} (1−α)W_α(i)`;
(ii) `lim_{α→1⁻} w_α(i) =: w(i) = ∑_k p_k(i)[c_{i|k}(f) − J_k m_{i|k}(f)]`;
(iii) `lim_{n→∞} E_f[w(X_n) | X_0 = i]/n = 0`;
(iv) the average cost optimality equation
`J(i) + w(i) = C(i,f) + ∑_j P_{ij}(f) w(j) ≥ min_a {C(i,a) + ∑_j P_{ij}(a) w(j)}` (6.6) holds;
(v) if `e` is a stationary policy realizing the minimum in (6.6) and the chain induced by `e` is
positive recurrent at `i`, then (6.6) is an equality at `i` and `J_e(i) = J(i)`. -/
theorem solution {S : Type*} {Act : Type*} [Fintype S] (M : MDC S Act)
    (f : StationaryPolicy M) (α₀ : ℝ) (hα₀ : α₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hf : ∀ α ∈ Set.Ioo α₀ 1, IsDiscountOptimal f.toPolicy α)
    (Z : Finset S) (hZ : IsDistinguishedSet (inducedChain M f) Z) (i : S) :
    let w : S → ℝ := relValue M f Z
    let rhs : S → Act → ℝ := fun j a => (M.C j a : ℝ) + ∑ k, (M.P j a k).toReal * w k
    let minRhs : S → ℝ := fun j => (M.A j).inf' (M.A_nonempty j) (rhs j)
    -- (i)
    Tendsto (fun α : ℝ => ENNReal.ofReal (1 - α) * Wdisc M f Z α i) (𝓝[<] 1)
        (𝓝 (avgValue M i)) ∧
    -- (ii)
    Tendsto (fun α : ℝ => wdisc M f Z α i) (𝓝[<] 1) (𝓝 (w i)) ∧
    -- (iii)
    Tendsto (fun n : ℕ => (∑ j, (nStep (inducedChain M f) n i j).toReal * w j) / (n : ℝ))
        atTop (𝓝 0) ∧
    -- (iv)
    ((avgValue M i).toReal + w i = rhs i (f.f i) ∧ rhs i (f.f i) ≥ minRhs i) ∧
    -- (v)
    (∀ e : StationaryPolicy M, (∀ j, rhs j (e.f j) = minRhs j) →
      PositiveRecurrent (inducedChain M e) i →
      (avgValue M i).toReal + w i = minRhs i ∧ avgCost e.toPolicy i = avgValue M i) := by
  exact bc_acoe_result M f α₀ hα₀ hf Z hZ i

#print axioms solution

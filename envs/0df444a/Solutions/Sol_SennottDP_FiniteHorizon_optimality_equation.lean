-- Prove2me | solution 1 for SennottDP.FiniteHorizon.optimality_equation
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-03T23:03:54.097734+00:00
-- url     : https://prove2.me/submissions/e85a1697-2758-4dcc-ad3c-385645be6aa9

import Mathlib
import Definitions.Def_SennottDP_FiniteHorizon_MDC
import Definitions.Def_SennottDP_FiniteHorizon_Criterion
import Definitions.Def_SennottDP_FiniteHorizon_ApproxSeq

set_option autoImplicit false

open scoped ENNReal NNReal Topology
open Filter


namespace SennottDP.FiniteHorizon
open scoped ENNReal NNReal
open Filter Topology
noncomputable section
variable {S Act : Type}

def fa_listEquiv (β : Type) : List β ≃ Unit ⊕ (β × List β) where
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

lemma fa_tsum_list {β : Type} (F : List β → ℝ≥0∞) :
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
end SennottDP.FiniteHorizon


namespace SennottDP.FiniteHorizon
open scoped ENNReal NNReal
open Filter Topology
noncomputable section
variable {S Act : Type}

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
end SennottDP.FiniteHorizon


namespace SennottDP.FiniteHorizon
open scoped ENNReal NNReal
open Classical Filter Topology
noncomputable section
variable {S Act : Type}

def fa_reverseEquiv (β : Type) : List β ≃ List β where
  toFun := List.reverse
  invFun := List.reverse
  left_inv := List.reverse_reverse
  right_inv := List.reverse_reverse

lemma fa_tsum_append {β : Type} (F : List β → ℝ≥0∞) :
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
end SennottDP.FiniteHorizon


namespace SennottDP.FiniteHorizon
open scoped ENNReal NNReal
open Classical Filter Topology
noncomputable section
variable {S Act : Type}

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
end SennottDP.FiniteHorizon


namespace SennottDP.FiniteHorizon
open scoped ENNReal NNReal
open Classical Filter Topology
noncomputable section

lemma fa_tsum_eq_term {ι : Type*} (F G : ι → ℝ≥0∞) (h : ∀ j, F j ≤ G j)
    (hfinite : (∑' j, F j) ≠ ⊤) (he : (∑' j, F j)=∑' j, G j) (j : ι) : F j=G j := by
  by_contra hn
  have hlt := ENNReal.tsum_lt_tsum hfinite h (lt_of_le_of_ne (h j) hn)
  rw [he] at hlt
  exact (lt_irrefl _ hlt)

lemma fa_finset_eq_term {ι : Type*} (s : Finset ι) (F G : ι → ℝ≥0∞)
    (h : ∀ j ∈ s, F j ≤ G j) (hfinite : (∑ j ∈ s, F j) ≠ ⊤)
    (he : (∑ j ∈ s, F j)=∑ j ∈ s, G j) (j : ι) (hj : j ∈ s) : F j=G j := by
  have hF : (∑' j : {j // j ∈ s}, F j)=∑ j ∈ s, F j := by
    rw [tsum_fintype,Finset.sum_coe_sort]
  have hG : (∑' j : {j // j ∈ s}, G j)=∑ j ∈ s, G j := by
    rw [tsum_fintype,Finset.sum_coe_sort]
  exact fa_tsum_eq_term (fun j : {j // j ∈ s} => F j) (fun j => G j)
    (fun j => h j j.2) (by rw [hF]; exact hfinite) (by rw [hF,hG,he]) ⟨j,hj⟩

lemma fa_weighted_min {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (q U : ι → ℝ≥0∞) (hq : ∑ j ∈ s, q j=1) :
    s.inf' hs U ≤ ∑ j ∈ s, q j*U j ∧
      ((∑ j ∈ s, q j*U j)=s.inf' hs U ↔ ∀ j ∈ s, q j ≠ 0 → U j=s.inf' hs U) := by
  let m := s.inf' hs U
  have hc : (∑ j ∈ s, q j*m)=m := by rw [← Finset.sum_mul,hq,one_mul]
  have hl (j : ι) (hj : j ∈ s) : m ≤ U j := Finset.inf'_le _ hj
  have hlo : m ≤ ∑ j ∈ s, q j*U j := by
    rw [← hc]
    exact Finset.sum_le_sum (fun j hj => mul_le_mul_right (hl j hj) (q j))
  refine ⟨hlo,?_,?_⟩
  · intro he j hj hqj
    by_cases hm : m=⊤
    · exact (top_le_iff.mp (hm ▸ hl j hj)).trans hm.symm
    · have hterm := fa_finset_eq_term s (fun j => q j*m) (fun j => q j*U j)
        (fun j hj => mul_le_mul_right (hl j hj) (q j))
        (by rw [hc]; exact hm) (hc.trans he.symm) j hj
      have hqfinite : q j ≠ ⊤ := by
        have hle : q j ≤ 1 := (Finset.single_le_sum (fun _ _ => bot_le) hj).trans_eq hq
        exact ne_of_lt (hle.trans_lt ENNReal.one_lt_top)
      exact ((ENNReal.mul_right_inj hqj hqfinite).mp hterm).symm
  · intro h
    calc
      _ = ∑ j ∈ s, q j*m := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hqj : q j=0
        · simp [hqj]
        · rw [h j hj hqj]
      _ = m := hc

end
end SennottDP.FiniteHorizon


namespace SennottDP.FiniteHorizon
open scoped ENNReal NNReal
open Classical Filter Topology
noncomputable section
variable {S Act : Type}

def fa_policyQ (M : MDC S Act) (F : S → ℝ≥0) (α : ℝ≥0)
    (θ : M.Policy) (n : ℕ) (i : S) (a : Act) : ℝ≥0∞ :=
  (M.C i a : ℝ≥0∞)+(α : ℝ≥0∞)*∑' j, M.P i a j*MDC.horizonCost F α (θ.shift i a) n j

lemma fa_horizon_Q (M : MDC S Act) (F : S → ℝ≥0) (α : ℝ≥0)
    (θ : M.Policy) (n : ℕ) (i : S) :
    MDC.horizonCost F α θ (n+1) i=∑ a ∈ M.A i, θ.σ [] i a*fa_policyQ M F α θ n i a := by
  rw [fa_horizon_rec]
  simp only [fa_policyQ,mul_add,Finset.sum_add_distrib,fa_initialAvg,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma fa_value_le_cost (M : MDC S Act) (F : S → ℝ≥0) (α : ℝ≥0)
    (θ : M.Policy) (n : ℕ) (i : S) : M.value F α n i ≤ MDC.horizonCost F α θ n i :=
  iInf_le _ θ

lemma fa_aux_le_policyQ (M : MDC S Act) (F : S → ℝ≥0) (α : ℝ≥0)
    (θ : M.Policy) (n : ℕ) (i : S) (a : Act) :
    M.aux F α (n+1) i a ≤ fa_policyQ M F α θ n i a := by
  simp only [MDC.aux,Nat.add_sub_cancel,fa_policyQ]
  exact add_le_add le_rfl (mul_le_mul_right (ENNReal.tsum_le_tsum
    (fun j => mul_le_mul_right (fa_value_le_cost M F α (θ.shift i a) n j) (M.P i a j))) _)

lemma fa_sigma_mem (M : MDC S Act) (θ : M.Policy) (i : S) (a : Act)
    (ha : θ.σ [] i a ≠ 0) : a ∈ M.A i := by
  by_contra hn
  exact ha (θ.σ_supp [] i a hn)

lemma fa_policy_optimal_at (M : MDC S Act) (F : S → ℝ≥0) (α : ℝ≥0) (hα : 0 < α)
    (θ : M.Policy) (n : ℕ) (i : S) :
    MDC.horizonCost F α θ (n+1) i=M.value F α (n+1) i ↔
      (∀ a, θ.σ [] i a ≠ 0 → a ∈ M.minSet F α (n+1) i) ∧
      (M.value F α (n+1) i < ⊤ → ∀ a j, θ.σ [] i a ≠ 0 → M.P i a j ≠ 0 →
        MDC.horizonCost F α (θ.shift i a) n j=M.value F α n j) := by
  let q := θ.σ [] i
  let Q := M.aux F α (n+1) i
  let D := fa_policyQ M F α θ n i
  let m := M.value F α (n+1) i
  have hmin : (M.A i).inf' (M.A_nonempty i) Q=m :=
    (fa_optimality_rec M F α (n+1) (by omega) i).symm
  have hq := θ.σ_sum [] i
  have havg := fa_weighted_min (M.A i) (M.A_nonempty i) q Q hq
  rw [hmin] at havg
  have hQD : ∀ a, Q a ≤ D a := fa_aux_le_policyQ M F α θ n i
  have hle : (∑ a ∈ M.A i, q a*Q a) ≤ ∑ a ∈ M.A i, q a*D a :=
    Finset.sum_le_sum (fun a _ => mul_le_mul_right (hQD a) (q a))
  have hcost : MDC.horizonCost F α θ (n+1) i=∑ a ∈ M.A i, q a*D a :=
    fa_horizon_Q M F α θ n i
  have hαne : (α : ℝ≥0∞) ≠ 0 := by exact_mod_cast ne_of_gt hα
  constructor
  · intro ho
    have hD : (∑ a ∈ M.A i, q a*D a)=m := hcost.symm.trans ho
    have hQ : (∑ a ∈ M.A i, q a*Q a)=m := le_antisymm (hle.trans_eq hD) havg.1
    have hcon := havg.2.mp hQ
    refine ⟨?_,?_⟩
    · intro a ha
      exact Finset.mem_filter.mpr ⟨fa_sigma_mem M θ i a ha,
        (hcon a (fa_sigma_mem M θ i a ha) ha).trans hmin.symm⟩
    · intro hm a j ha hp
      have haA := fa_sigma_mem M θ i a ha
      have hterm := fa_finset_eq_term (M.A i) (fun a => q a*Q a) (fun a => q a*D a)
        (fun a _ => mul_le_mul_right (hQD a) (q a)) (by rw [hQ]; exact ne_of_lt hm)
        (hQ.trans hD.symm) a haA
      have hqfin : q a ≠ ⊤ := by
        have hh : q a ≤ 1 := (Finset.single_le_sum (fun _ _ => bot_le) haA).trans_eq hq
        exact ne_of_lt (hh.trans_lt ENNReal.one_lt_top)
      have he : Q a=D a := (ENNReal.mul_right_inj ha hqfin).mp hterm
      have hex : (∑' k, M.P i a k*M.value F α n k)=
          ∑' k, M.P i a k*MDC.horizonCost F α (θ.shift i a) n k := by
        change (M.C i a : ℝ≥0∞)+(α : ℝ≥0∞)*(∑' k, M.P i a k*M.value F α n k)=
          (M.C i a : ℝ≥0∞)+(α : ℝ≥0∞)*
            (∑' k, M.P i a k*MDC.horizonCost F α (θ.shift i a) n k) at he
        exact (ENNReal.mul_right_inj hαne ENNReal.coe_ne_top).mp
          ((ENNReal.add_right_inj ENNReal.coe_ne_top).mp he)
      have hsumfin : (∑' k, M.P i a k*M.value F α n k) ≠ ⊤ := by
        intro ht
        have htop : Q a=⊤ := by simp [Q,MDC.aux,ht,hαne]
        have hh := hcon a haA ha
        rw [htop] at hh
        exact (ne_of_lt hm) hh.symm
      have hj := fa_tsum_eq_term
        (fun k => M.P i a k*M.value F α n k)
        (fun k => M.P i a k*MDC.horizonCost F α (θ.shift i a) n k)
        (fun k => mul_le_mul_right (fa_value_le_cost M F α (θ.shift i a) n k) (M.P i a k))
        hsumfin hex j
      have hpfin : M.P i a j ≠ ⊤ := by
        have hh : M.P i a j ≤ 1 := (ENNReal.le_tsum j).trans_eq (M.P_sum i a haA)
        exact ne_of_lt (hh.trans_lt ENNReal.one_lt_top)
      exact ((ENNReal.mul_right_inj hp hpfin).mp hj).symm
  · rintro ⟨hcon,hcont⟩
    change MDC.horizonCost F α θ (n+1) i=m
    by_cases hm : m=⊤
    · exact le_antisymm (by rw [hm]; exact le_top) (fa_value_le_cost M F α θ (n+1) i)
    · have hQ : (∑ a ∈ M.A i, q a*Q a)=m := havg.2.mpr (by
        intro a _ ha
        exact ((Finset.mem_filter.mp (hcon a ha)).2).trans hmin)
      rw [hcost,← hQ]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : q a=0
      · simp [ha]
      · congr 1
        change (M.C i a : ℝ≥0∞)+(α : ℝ≥0∞)*
            (∑' j, M.P i a j*MDC.horizonCost F α (θ.shift i a) n j)=
          (M.C i a : ℝ≥0∞)+(α : ℝ≥0∞)*(∑' j, M.P i a j*M.value F α n j)
        congr 2
        apply tsum_congr
        intro j
        by_cases hp : M.P i a j=0
        · simp [hp]
        · rw [hcont (lt_top_iff_ne_top.mpr hm) a j ha hp]

lemma fa_optimality_result (M : MDC S Act) (F : S → ℝ≥0) (α : ℝ≥0) (hα : 0 < α) :
    (∀ n, 1 ≤ n → ∀ i, M.value F α n i = (M.A i).inf' (M.A_nonempty i) (M.aux F α n i)) ∧
    (∀ θ : M.Policy, M.IsOptimal F α 1 θ ↔
      ∀ i a, θ.σ [] i a ≠ 0 → a ∈ M.minSet F α 1 i) ∧
    (∀ n, 2 ≤ n → ∀ θ : M.Policy, M.IsOptimal F α n θ ↔
      ∀ i, (∀ a, θ.σ [] i a ≠ 0 → a ∈ M.minSet F α n i) ∧
        (M.value F α n i < ⊤ → ∀ a j, θ.σ [] i a ≠ 0 → M.P i a j ≠ 0 →
          MDC.horizonCost F α (θ.shift i a) (n - 1) j = M.value F α (n - 1) j)) := by
  refine ⟨fa_optimality_rec M F α,?_,?_⟩
  · intro θ
    constructor
    · intro h i
      exact ((fa_policy_optimal_at M F α hα θ 0 i).mp (h i)).1
    · intro h i
      apply (fa_policy_optimal_at M F α hα θ 0 i).mpr
      refine ⟨h i,?_⟩
      intro _ a j _ _
      rw [fa_horizon_zero,fa_value_eq]
      rfl
  · intro n hn θ
    have he : n=(n-1)+1 := by omega
    unfold MDC.IsOptimal
    simpa only [← he] using
      (forall_congr' (fun i => fa_policy_optimal_at M F α hα θ (n-1) i))

end
end SennottDP.FiniteHorizon

open SennottDP.FiniteHorizon

/-- Theorem 3.1.2 (Sennott, pp. 36–37), with a correction to the necessity of (ii)(2).
Let `0 < α ≤ 1` and a nonnegative terminal cost `F`. The finite horizon value function satisfies
the finite horizon optimality equation (3.2)
`v_{α,n}(i) = min_{a ∈ A_i} {C(i,a) + α ∑_j P_ij(a) v_{α,n−1}(j)}`, `i ∈ S`, `n ≥ 1`, and:
(i) a (general) policy `θ` is optimal for the 1 horizon iff for every initial state `i` the
distribution `θ(· | i)` is concentrated on `B_i(α, 1)`;
(ii) for `n ≥ 2`, `θ` is optimal for the `n` horizon iff for every initial state `i`:
(1) `θ(· | i)` is concentrated on `B_i(α, n)`, and (2) whenever `v_{α,n}(i) < ∞`, for every
action `a` with `θ(a | i) > 0` and every state `j` with `P_ij(a) > 0`, the continuation policy
`ψ(i, a, j)` of `θ` is optimal for the `n − 1` horizon at `j`.
The guard `v_{α,n}(i) < ∞` in (2) is not in the book; without it the "only if" fails when
`v_{α,n}(i) = ∞` (then every policy is optimal at `i`). -/
theorem solution {S Act : Type} [Countable S] (M : MDC S Act) (F : S → ℝ≥0)
    (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (∀ n, 1 ≤ n → ∀ i, M.value F α n i = (M.A i).inf' (M.A_nonempty i) (M.aux F α n i)) ∧
    (∀ θ : M.Policy, M.IsOptimal F α 1 θ ↔
      ∀ i a, θ.σ [] i a ≠ 0 → a ∈ M.minSet F α 1 i) ∧
    (∀ n, 2 ≤ n → ∀ θ : M.Policy, M.IsOptimal F α n θ ↔
      ∀ i, (∀ a, θ.σ [] i a ≠ 0 → a ∈ M.minSet F α n i) ∧
        (M.value F α n i < ⊤ → ∀ a j, θ.σ [] i a ≠ 0 → M.P i a j ≠ 0 →
          MDC.horizonCost F α (θ.shift i a) (n - 1) j = M.value F α (n - 1) j)) := by
  exact fa_optimality_result M F α hα0

#print axioms solution

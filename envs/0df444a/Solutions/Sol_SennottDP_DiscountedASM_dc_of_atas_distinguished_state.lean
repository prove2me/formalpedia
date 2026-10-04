-- Prove2me | solution 1 for SennottDP.DiscountedASM.dc_of_atas_distinguished_state
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T00:00:41.644091+00:00
-- url     : https://prove2.me/submissions/fa531c47-4e59-49ba-be8d-2c54f4386683

import Mathlib
import Definitions.Def_SennottDP_DiscountedASM_MDC
import Definitions.Def_SennottDP_DiscountedASM_ApproxSeq
import Definitions.Def_SennottDP_FiniteHorizon_ApproxSeq

set_option autoImplicit false

open scoped ENNReal NNReal
open Classical Filter Topology


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
end SennottDP.FiniteHorizon


namespace SennottDP.FiniteHorizon
open scoped ENNReal NNReal
open Classical Filter Topology
noncomputable section
variable {S Act : Type} [Countable S]

lemma fa_eventually_member (M : MDC S Act) (AS : M.ApproxSeq) (i : S) :
    ∀ᶠ N in atTop, AS.N₀ ≤ N ∧ i ∈ AS.SN N := by
  obtain ⟨N,hN,hi⟩ := AS.SN_spec.2.2 i
  exact eventually_atTop.mpr ⟨N,fun K hK => ⟨hN.trans hK,AS.SN_spec.2.1 N K hN hK hi⟩⟩

def fa_PN (M : MDC S Act) (AS : M.ApproxSeq) (N : ℕ) (i : S) (a : Act) (j : S) : ℝ≥0∞ :=
  if j ∈ AS.SN N then AS.PN N i a j else 0

lemma fa_PN_tendsto (M : MDC S Act) (AS : M.ApproxSeq) (i : S) (a : Act) (ha : a ∈ M.A i) (j : S) :
    Tendsto (fun N => fa_PN M AS N i a j) atTop (𝓝 (M.P i a j)) := by
  apply (AS.PN_tendsto i a ha j).congr'
  filter_upwards [fa_eventually_member M AS j] with N hN
  simp [fa_PN,hN.2]

lemma fa_PN_sum (M : MDC S Act) (AS : M.ApproxSeq) (N : ℕ) (hN : AS.N₀ ≤ N)
    (i : S) (hi : i ∈ AS.SN N) (a : Act) (ha : a ∈ M.A i) :
    (∑' j, fa_PN M AS N i a j)=1 := by
  rw [tsum_eq_sum (s := AS.SN N)]
  · have he : (∑ j ∈ AS.SN N, fa_PN M AS N i a j)=∑ j ∈ AS.SN N, AS.PN N i a j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [fa_PN,hj]
    rw [he]
    exact AS.PN_sum N hN i hi a ha
  · intro j hj
    simp [fa_PN,hj]

lemma fa_valueN_zero (M : MDC S Act) (AS : M.ApproxSeq) (F : S → ℝ≥0) (α : ℝ≥0) (i : S) :
    Tendsto (fun N => AS.valueN F α 0 N i) atTop (𝓝 (M.value F α 0 i)) := by
  rw [fa_value_eq]
  change Tendsto _ atTop (𝓝 (F i : ℝ≥0∞))
  apply tendsto_const_nhds.congr'
  filter_upwards [fa_eventually_member M AS i] with N hN
  simp [MDC.ApproxSeq.valueN,hN.1,hN.2,fa_value_eq,fa_iter]

lemma fa_valueN_rec (M : MDC S Act) (AS : M.ApproxSeq) (F : S → ℝ≥0) (α : ℝ≥0) (n : ℕ) (i : S) :
    ∀ᶠ N in atTop, AS.valueN F α (n+1) N i=(M.A i).inf' (M.A_nonempty i)
      (fun a => (M.C i a : ℝ≥0∞)+(α : ℝ≥0∞)*∑' j, fa_PN M AS N i a j*AS.valueN F α n N j) := by
  filter_upwards [fa_eventually_member M AS i] with N hN
  rw [MDC.ApproxSeq.valueN,dif_pos hN,
    fa_optimality_rec (AS.toMDC N hN.1) (fun j => F j.1) α (n+1) (by omega)]
  change (M.A i).inf' (M.A_nonempty i)
      (fun a => (M.C i a : ℝ≥0∞)+(α : ℝ≥0∞)*∑' j : AS.SN N,
        AS.PN N i a j.1*(AS.toMDC N hN.1).value (fun j => F j.1) α ((n+1)-1) j)= _
  simp only [Nat.add_sub_cancel]
  congr 1
  funext a
  congr 1
  congr 1
  calc
    _ = ∑' j : AS.SN N, AS.PN N i a j.1*AS.valueN F α n N j.1 := by
      apply tsum_congr
      intro j
      simp [MDC.ApproxSeq.valueN,hN.1,j.2]
    _ = ∑ j ∈ AS.SN N, AS.PN N i a j*AS.valueN F α n N j :=
      Finset.tsum_subtype (AS.SN N) (fun j : S => AS.PN N i a j*AS.valueN F α n N j)
    _ = ∑ j ∈ AS.SN N, fa_PN M AS N i a j*AS.valueN F α n N j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [fa_PN,hj]
    _ = _ := by
      symm
      apply tsum_eq_sum
      intro j hj
      simp [fa_PN,hj]

lemma fa_action_lower (M : MDC S Act) (AS : M.ApproxSeq) (F : S → ℝ≥0) (α : ℝ≥0) (n : ℕ)
    (hn : ∀ j, M.value F α n j ≤ liminf (fun N => AS.valueN F α n N j) atTop)
    (i : S) (a : Act) (ha : a ∈ M.A i) :
    fa_Q M α (M.value F α n) i a ≤ liminf (fun N => (M.C i a : ℝ≥0∞)+(α : ℝ≥0∞)*
      ∑' j, fa_PN M AS N i a j*AS.valueN F α n N j) atTop := by
  have hp (j : S) : M.P i a j*M.value F α n j ≤
      liminf (fun N => fa_PN M AS N i a j*AS.valueN F α n N j) atTop := by
    have hh := ENNReal.le_liminf_mul (f := atTop) (u := fun N => fa_PN M AS N i a j)
      (v := fun N => AS.valueN F α n N j)
    rw [(fa_PN_tendsto M AS i a ha j).liminf_eq] at hh
    exact (mul_le_mul_right (hn j) (M.P i a j)).trans hh
  have hs : (∑' j, M.P i a j*M.value F α n j) ≤
      liminf (fun N => ∑' j, fa_PN M AS N i a j*AS.valueN F α n N j) atTop :=
    (ENNReal.tsum_le_tsum hp).trans (fa_tsum_liminf _)
  rw [fa_liminf_add,ENNReal.liminf_const_mul_of_ne_top ENNReal.coe_ne_top]
  unfold fa_Q
  gcongr

lemma fa_liminf_all (M : MDC S Act) (AS : M.ApproxSeq) (F : S → ℝ≥0) (α : ℝ≥0) (n : ℕ) (i : S) :
    M.value F α n i ≤ liminf (fun N => AS.valueN F α n N i) atTop := by
  induction n generalizing i with
  | zero => rw [(fa_valueN_zero M AS F α i).liminf_eq]
  | succ n ih =>
    rw [fa_optimality_rec M F α (n+1) (by omega)]
    change (M.A i).inf' (M.A_nonempty i) (fa_Q M α (M.value F α n) i) ≤ _
    calc
      _ ≤ (M.A i).inf' (M.A_nonempty i) (fun a => liminf (fun N =>
          (M.C i a : ℝ≥0∞)+(α : ℝ≥0∞)*∑' j, fa_PN M AS N i a j*AS.valueN F α n N j) atTop) :=
        fa_inf'_mono _ _ _ _ (fun a ha => fa_action_lower M AS F α n ih i a ha)
      _ = liminf (fun N => (M.A i).inf' (M.A_nonempty i) (fun a =>
          (M.C i a : ℝ≥0∞)+(α : ℝ≥0∞)*∑' j, fa_PN M AS N i a j*AS.valueN F α n N j)) atTop :=
        fa_inf'_liminf _ _ _
      _ = _ := liminf_congr ((fa_valueN_rec M AS F α n i).mono (fun _ he => he.symm))

lemma fa_liminf_result (M : MDC S Act) (F : S → ℝ≥0) (α : ℝ≥0) (AS : M.ApproxSeq) :
    (∀ i, Tendsto (fun N => AS.valueN F α 0 N i) atTop (𝓝 (M.value F α 0 i))) ∧
      (∀ n, 1 ≤ n → ∀ i, M.value F α n i ≤ liminf (fun N => AS.valueN F α n N i) atTop) :=
  ⟨fa_valueN_zero M AS F α,fun n _ i => fa_liminf_all M AS F α n i⟩

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


namespace SennottDP.DiscountedASM
open scoped ENNReal NNReal
open Classical Filter Topology
noncomputable section
variable {S Act : Type} [Countable S]

def da_model (M : MDC S Act) : SennottDP.FiniteHorizon.MDC S Act where
  A := M.A
  A_nonempty := M.A_nonempty
  C := M.C
  P := M.P
  P_sum := M.P_sum

def da_policy (M : MDC S Act) (θ : M.Policy) : (da_model M).Policy where
  σ := θ.σ
  σ_sum := θ.σ_sum
  σ_supp := θ.σ_supp

def da_policyBack (M : MDC S Act) (θ : (da_model M).Policy) : M.Policy where
  σ := θ.σ
  σ_sum := θ.σ_sum
  σ_supp := θ.σ_supp

lemma da_policy_inverse (M : MDC S Act) (θ : (da_model M).Policy) :
    da_policy M (da_policyBack M θ)=θ := by cases θ; rfl

lemma da_hist (M : MDC S Act) (θ : M.Policy) (i : S) (t : ℕ) (h : List (S × Act)) (j : S) :
    SennottDP.FiniteHorizon.MDC.histProb (da_policy M θ) i t h j=MDC.histProb θ i t h j := by
  induction t generalizing h j with
  | zero => cases h <;> rfl
  | succ t ih =>
    cases h with
    | nil => rfl
    | cons p h =>
      rcases p with ⟨k,a⟩
      simp only [SennottDP.FiniteHorizon.MDC.histProb,MDC.histProb,ih]
      rfl

lemma da_expectedCost (M : MDC S Act) (θ : M.Policy) (i : S) (t : ℕ) :
    SennottDP.FiniteHorizon.MDC.expectedCost (da_policy M θ) i t=MDC.expectedCost θ i t := by
  rw [SennottDP.FiniteHorizon.fa_expectedCost]
  unfold MDC.expectedCost
  apply tsum_congr
  intro h
  apply tsum_congr
  intro j
  rw [Finset.mul_sum,da_hist]
  apply Finset.sum_congr rfl
  intro a _
  simp only [da_policy,da_model,mul_assoc]

lemma da_horizon (M : MDC S Act) (θ : M.Policy) (α : ℝ≥0) (n : ℕ) (i : S) :
    SennottDP.FiniteHorizon.MDC.horizonCost (fun _ => 0) α (da_policy M θ) n i=
      MDC.horizonCost θ α n i := by
  unfold SennottDP.FiniteHorizon.MDC.horizonCost MDC.horizonCost
  rw [SennottDP.FiniteHorizon.fa_expectedTerminal]
  simp only [SennottDP.FiniteHorizon.fa_expect,ENNReal.coe_zero,mul_zero,tsum_zero,add_zero]
  apply Finset.sum_congr rfl
  intro t _
  rw [da_expectedCost]

lemma da_horizonValue (M : MDC S Act) (α : ℝ≥0) (n : ℕ) (i : S) :
    M.horizonValue α n i=(da_model M).value (fun _ => 0) α n i := by
  apply le_antisymm
  · apply le_iInf
    intro θ
    have hh := iInf_le (fun ψ : M.Policy => MDC.horizonCost ψ α n i) (da_policyBack M θ)
    rw [← da_horizon,da_policy_inverse] at hh
    exact hh
  · apply le_iInf
    intro θ
    exact (iInf_le _ (da_policy M θ)).trans_eq (da_horizon M θ α n i)

def da_AS (M : MDC S Act) (Δs : ApproxSeq M) : (da_model M).ApproxSeq where
  N₀ := Δs.N0
  SN := Δs.SN
  SN_spec := ⟨Δs.SN_nonempty,Δs.SN_mono,Δs.SN_cover⟩
  PN := Δs.PN
  PN_sum := Δs.PN_sum
  PN_tendsto := Δs.PN_lim

lemma da_trunc_model (M : MDC S Act) (Δs : ApproxSeq M) (N : ℕ) (hN : Δs.N0 ≤ N) :
    da_model (Δs.truncMDC N hN)=(da_AS M Δs).toMDC N hN := rfl

lemma da_horizonN (M : MDC S Act) (Δs : ApproxSeq M) (α : ℝ≥0) (n N : ℕ) (i : S)
    (hN : Δs.N0 ≤ N) (hi : i ∈ Δs.SN N) :
    (da_AS M Δs).valueN (fun _ => 0) α n N i=(Δs.truncMDC N hN).horizonValue α n ⟨i,hi⟩ := by
  rw [da_horizonValue,da_trunc_model]
  simp [SennottDP.FiniteHorizon.MDC.ApproxSeq.valueN,da_AS,hN,hi]

end
end SennottDP.DiscountedASM


namespace SennottDP.DiscountedASM
open scoped ENNReal NNReal
open Classical Filter Topology
open SennottDP.FiniteHorizon
noncomputable section
variable {S Act : Type} [Countable S]

lemma da_Q_mono (M : MDC S Act) (α : ℝ≥0) (U W : S → ℝ≥0∞)
    (h : ∀ j, U j ≤ W j) (i : S) (a : Act) :
    fa_Q (da_model M) α U i a ≤ fa_Q (da_model M) α W i a := by
  unfold fa_Q
  exact add_le_add le_rfl (mul_le_mul_right
    (ENNReal.tsum_le_tsum (fun j => mul_le_mul_right (h j) (M.P i a j))) _)

lemma da_T_mono (M : MDC S Act) (α : ℝ≥0) (U W : S → ℝ≥0∞)
    (h : ∀ j, U j ≤ W j) (i : S) : fa_T (da_model M) α U i ≤ fa_T (da_model M) α W i :=
  fa_inf'_mono _ _ _ _ (fun a _ => da_Q_mono M α U W h i a)

lemma da_Q_iSup (M : MDC S Act) (α : ℝ≥0) (U : ℕ → S → ℝ≥0∞)
    (hU : ∀ j, Monotone (fun n => U n j)) (i : S) (a : Act) :
    fa_Q (da_model M) α (fun j => ⨆ n, U n j) i a=⨆ n, fa_Q (da_model M) α (U n) i a := by
  unfold fa_Q
  simp only [da_model]
  simp_rw [ENNReal.mul_iSup]
  rw [fa_tsum_iSup (fun n j => M.P i a j*U n j)
    (fun j r s hrs => mul_le_mul_right (hU j hrs) (M.P i a j))]
  rw [ENNReal.mul_iSup,ENNReal.add_iSup]

lemma da_T_iSup (M : MDC S Act) (α : ℝ≥0) (U : ℕ → S → ℝ≥0∞)
    (hU : ∀ j, Monotone (fun n => U n j)) (i : S) :
    fa_T (da_model M) α (fun j => ⨆ n, U n j) i=⨆ n, fa_T (da_model M) α (U n) i := by
  unfold fa_T
  simp_rw [da_Q_iSup M α U hU]
  exact fa_inf'_iSup _ _ _ (fun a _ r s hrs => da_Q_mono M α _ _ (fun j => hU j hrs) i a)

def da_iter (M : MDC S Act) (α : ℝ≥0) : ℕ → S → ℝ≥0∞ := fa_iter (da_model M) (fun _ => 0) α

lemma da_iter_mono (M : MDC S Act) (α : ℝ≥0) (i : S) : Monotone (fun n => da_iter M α n i) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n generalizing i with
  | zero => exact bot_le
  | succ n ih => exact da_T_mono M α _ _ ih i

def da_limit (M : MDC S Act) (α : ℝ≥0) (i : S) : ℝ≥0∞ := ⨆ n, da_iter M α n i

lemma da_limit_fixed (M : MDC S Act) (α : ℝ≥0) (i : S) :
    da_limit M α i=fa_T (da_model M) α (da_limit M α) i := by
  unfold da_limit
  rw [da_T_iSup M α (da_iter M α) (da_iter_mono M α)]
  change (⨆ n, da_iter M α n i)=⨆ n, da_iter M α (n+1) i
  apply le_antisymm
  · apply iSup_le
    intro n
    exact (da_iter_mono M α i (Nat.le_succ n)).trans (le_iSup (fun n => da_iter M α (n+1) i) n)
  · apply iSup_le
    intro n
    exact le_iSup (fun n => da_iter M α n i) (n+1)

lemma da_stationary_supersolution (M : MDC S Act) (α : ℝ≥0) (f : S → Act)
    (hf : ∀ i, f i ∈ M.A i) (U : S → ℝ≥0∞)
    (hU : ∀ i, fa_Q (da_model M) α U i (f i) ≤ U i) :
    ∀ i, MDC.discCost (M.ofStationary f hf) α i ≤ U i := by
  let θ := da_policy M (M.ofStationary f hf)
  have hshift (i : S) (a : Act) : θ.shift i a=θ := rfl
  have hcost (n : ℕ) (i : S) : SennottDP.FiniteHorizon.MDC.horizonCost (fun _ => 0) α θ n i ≤ U i := by
    induction n generalizing i with
    | zero => simp [fa_horizon_zero]
    | succ n ih =>
      have hrec : SennottDP.FiniteHorizon.MDC.horizonCost (fun _ => 0) α θ (n+1) i=
          (M.C i (f i) : ℝ≥0∞)+(α : ℝ≥0∞)*∑' j, M.P i (f i) j*
            SennottDP.FiniteHorizon.MDC.horizonCost (fun _ => 0) α θ n j := by
        rw [fa_horizon_rec]
        simp only [fa_initialAvg,hshift]
        simp [θ,da_policy,da_model,MDC.ofStationary,hf i]
      rw [hrec]
      apply le_trans ?_ (hU i)
      exact add_le_add le_rfl (mul_le_mul_right (ENNReal.tsum_le_tsum
        (fun j => mul_le_mul_right (ih j) (M.P i (f i) j))) _)
  intro i
  rw [MDC.discCost,ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro n
  have hc := hcost n i
  change SennottDP.FiniteHorizon.MDC.horizonCost (fun _ => 0) α
    (da_policy M (M.ofStationary f hf)) n i ≤ U i at hc
  rw [da_horizon] at hc
  exact hc

lemma da_value_eq_limit (M : MDC S Act) (α : ℝ≥0) : M.value α=da_limit M α := by
  have hl (i : S) : da_limit M α i ≤ M.value α i := by
    apply iSup_le
    intro n
    apply le_iInf
    intro θ
    exact (fa_iter_le_cost (da_model M) (fun _ => 0) (da_policy M θ) α n i).trans
      ((da_horizon M θ α n i).le.trans (ENNReal.sum_le_tsum (Finset.range n)))
  obtain ⟨f,hf⟩ := fa_selector (da_model M) α (da_limit M α)
  have hc := da_stationary_supersolution M α f.1 f.2 (da_limit M α)
    (fun i => (hf i).trans (da_limit_fixed M α i).symm |>.le)
  ext i
  exact le_antisymm ((iInf_le _ (M.ofStationary f.1 f.2)).trans (hc i)) (hl i)

lemma da_value_fixed (M : MDC S Act) (α : ℝ≥0) (i : S) :
    M.value α i=fa_T (da_model M) α (M.value α) i := by
  rw [da_value_eq_limit]
  exact da_limit_fixed M α i

lemma da_horizonValue_eq_iter (M : MDC S Act) (α : ℝ≥0) (n : ℕ) : M.horizonValue α n=da_iter M α n := by
  funext i
  rw [da_horizonValue,fa_value_eq]
  rfl

lemma da_optimal_selector (M : MDC S Act) (α : ℝ≥0) (f : S → Act) (hf : ∀ i, f i ∈ M.A i)
    (he : ∀ i, fa_Q (da_model M) α (M.value α) i (f i)=M.value α i) :
    ∀ i, MDC.discCost (M.ofStationary f hf) α i=M.value α i := by
  intro i
  exact le_antisymm (da_stationary_supersolution M α f hf (M.value α) (fun i => (he i).le) i)
    (iInf_le _ (M.ofStationary f hf))

end
end SennottDP.DiscountedASM


namespace SennottDP.DiscountedASM
open scoped ENNReal NNReal
open Classical Filter Topology
open SennottDP.FiniteHorizon
noncomputable section
variable {S Act : Type} [Countable S]

lemma da_horizon_le_value (M : MDC S Act) (α : ℝ≥0) (n : ℕ) (i : S) :
    M.horizonValue α n i ≤ M.value α i := by
  rw [da_horizonValue_eq_iter,da_value_eq_limit]
  exact le_iSup (fun n => da_iter M α n i) n

lemma da_finite_le_VN (M : MDC S Act) (Δs : ApproxSeq M) (α : ℝ≥0) (n N : ℕ) (i : S) :
    (da_AS M Δs).valueN (fun _ => 0) α n N i ≤ Δs.VN α N i := by
  by_cases h : Δs.N0 ≤ N ∧ i ∈ Δs.SN N
  · rw [da_horizonN M Δs α n N i h.1 h.2,ApproxSeq.VN,dif_pos h]
    exact da_horizon_le_value (Δs.truncMDC N h.1) α n ⟨i,h.2⟩
  · simp [SennottDP.FiniteHorizon.MDC.ApproxSeq.valueN,da_AS,h]

lemma da_liminf (M : MDC S Act) (Δs : ApproxSeq M) (α : ℝ≥0) (i : S) :
    M.value α i ≤ liminf (fun N => Δs.VN α N i) atTop := by
  rw [da_value_eq_limit]
  apply iSup_le
  intro n
  have hh := fa_liminf_all (da_model M) (da_AS M Δs) (fun _ => 0) α n i
  rw [fa_value_eq] at hh
  exact hh.trans (liminf_le_liminf (Eventually.of_forall (fun N => da_finite_le_VN M Δs α n N i)))

def da_actionN (M : MDC S Act) (Δs : ApproxSeq M) (α : ℝ≥0) (N : ℕ) (i : S) (a : Act) : ℝ≥0∞ :=
  (M.C i a : ℝ≥0∞)+(α : ℝ≥0∞)*∑' j, fa_PN (da_model M) (da_AS M Δs) N i a j*Δs.VN α N j

lemma da_actionN_sum (M : MDC S Act) (Δs : ApproxSeq M) (α : ℝ≥0) (N : ℕ) (i : S) (a : Act) :
    da_actionN M Δs α N i a=(M.C i a : ℝ≥0∞)+(α : ℝ≥0∞)*
      ∑ j ∈ Δs.SN N, Δs.PN N i a j*Δs.VN α N j := by
  unfold da_actionN
  congr 1
  congr 1
  rw [tsum_eq_sum (s := Δs.SN N)]
  · apply Finset.sum_congr rfl
    intro j hj
    simp [fa_PN,da_AS,hj]
  · intro j hj
    simp [fa_PN,da_AS,hj]

lemma da_VN_at_rec (M : MDC S Act) (Δs : ApproxSeq M) (α : ℝ≥0) (N : ℕ)
    (hN : Δs.N0 ≤ N) (i : S) (hi : i ∈ Δs.SN N) :
    Δs.VN α N i=(M.A i).inf' (M.A_nonempty i) (da_actionN M Δs α N i) := by
  rw [ApproxSeq.VN,dif_pos ⟨hN,hi⟩,da_value_fixed (Δs.truncMDC N hN) α ⟨i,hi⟩]
  change (M.A i).inf' (M.A_nonempty i) (fun a => (M.C i a : ℝ≥0∞)+(α : ℝ≥0∞)*
    ∑' j : Δs.SN N, Δs.PN N i a j.1*(Δs.truncMDC N hN).value α j)=_
  congr 1
  funext a
  rw [da_actionN_sum]
  congr 1
  congr 1
  calc
    _ = ∑' j : Δs.SN N, Δs.PN N i a j.1*Δs.VN α N j.1 := by
      apply tsum_congr
      intro j
      simp [ApproxSeq.VN,hN,j.2]
    _ = _ := Finset.tsum_subtype (Δs.SN N) (fun j : S => Δs.PN N i a j*Δs.VN α N j)

end
end SennottDP.DiscountedASM


namespace SennottDP.FiniteHorizon
open scoped ENNReal NNReal
open Classical Filter Topology
noncomputable section
variable {S Act : Type} [Countable S]

lemma fa_fh_convergence (M : MDC S Act) (F : S → ℝ≥0) (α : ℝ≥0) (AS : M.ApproxSeq) (n : ℕ) :
    (∀ i, Tendsto (fun N => AS.valueN F α n N i) atTop (𝓝 (M.value F α n i)) ∧
      M.value F α n i < ⊤) ↔ AS.FH F α n := by
  constructor
  · intro h i
    rw [(h i).1.limsup_eq]
    exact ⟨(h i).2,le_rfl⟩
  · intro h i
    have hl := fa_liminf_all M AS F α n i
    have hh : liminf (fun N => AS.valueN F α n N i) atTop ≤
        limsup (fun N => AS.valueN F α n N i) atTop := liminf_le_limsup
    exact ⟨tendsto_of_le_liminf_of_limsup_le hl (h i).2,hl.trans_lt (hh.trans_lt (h i).1)⟩

def fa_subsequence (M : MDC S Act) (AS : M.ApproxSeq) (φ : ℕ → ℕ) (hφ : StrictMono φ) : M.ApproxSeq where
  N₀ := AS.N₀
  SN N := AS.SN (φ N)
  SN_spec := by
    refine ⟨?_,?_,?_⟩
    · intro N hN
      exact AS.SN_spec.1 (φ N) (hN.trans (hφ.id_le N))
    · intro N K hN hNK
      exact AS.SN_spec.2.1 (φ N) (φ K) (hN.trans (hφ.id_le N)) (hφ.monotone hNK)
    · intro i
      obtain ⟨N,hN,hi⟩ := AS.SN_spec.2.2 i
      exact ⟨N,hN,AS.SN_spec.2.1 N (φ N) hN (hφ.id_le N) hi⟩
  PN N := AS.PN (φ N)
  PN_sum N hN := AS.PN_sum (φ N) (hN.trans (hφ.id_le N))
  PN_tendsto i a ha j := (AS.PN_tendsto i a ha j).comp hφ.tendsto_atTop

lemma fa_valueN_subsequence (M : MDC S Act) (AS : M.ApproxSeq) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (F : S → ℝ≥0) (α : ℝ≥0) (n N : ℕ) (hN : AS.N₀ ≤ N) (i : S) :
    (fa_subsequence M AS φ hφ).valueN F α n N i=AS.valueN F α n (φ N) i := by
  have hNφ : AS.N₀ ≤ φ N := hN.trans (hφ.id_le N)
  by_cases hi : i ∈ AS.SN (φ N)
  · simp [MDC.ApproxSeq.valueN,fa_subsequence,hN,hNφ,hi,MDC.ApproxSeq.toMDC]
  · simp [MDC.ApproxSeq.valueN,fa_subsequence,hN,hNφ,hi]

lemma fa_trunc_action (M : MDC S Act) (AS : M.ApproxSeq) (F : S → ℝ≥0) (α : ℝ≥0)
    (n N : ℕ) (hN : AS.N₀ ≤ N) (i : AS.SN N) (a : Act) :
    (AS.toMDC N hN).aux (fun j => F j.1) α n i a=
      (M.C i.1 a : ℝ≥0∞)+(α : ℝ≥0∞)*∑' j, fa_PN M AS N i.1 a j*AS.valueN F α (n-1) N j := by
  unfold MDC.aux
  change (M.C i.1 a : ℝ≥0∞)+(α : ℝ≥0∞)*∑' j : AS.SN N,
      AS.PN N i.1 a j.1*(AS.toMDC N hN).value (fun j => F j.1) α (n-1) j= _
  congr 1
  congr 1
  calc
    _ = ∑' j : AS.SN N, AS.PN N i.1 a j.1*AS.valueN F α (n-1) N j.1 := by
      apply tsum_congr
      intro j
      simp [MDC.ApproxSeq.valueN,hN,j.2]
    _ = ∑ j ∈ AS.SN N, AS.PN N i.1 a j*AS.valueN F α (n-1) N j :=
      Finset.tsum_subtype (AS.SN N) (fun j : S => AS.PN N i.1 a j*AS.valueN F α (n-1) N j)
    _ = ∑ j ∈ AS.SN N, fa_PN M AS N i.1 a j*AS.valueN F α (n-1) N j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [fa_PN,hj]
    _ = _ := by
      symm
      apply tsum_eq_sum
      intro j hj
      simp [fa_PN,hj]

lemma fa_min_actionN (M : MDC S Act) (AS : M.ApproxSeq) (F : S → ℝ≥0) (α : ℝ≥0)
    (n : ℕ) (hn : 1 ≤ n) (N : ℕ) (hN : AS.N₀ ≤ N) (i : AS.SN N) (a : Act)
    (ha : a ∈ AS.minSetN F α n N hN i) :
    (M.C i.1 a : ℝ≥0∞)+(α : ℝ≥0∞)*∑' j, fa_PN M AS N i.1 a j*AS.valueN F α (n-1) N j=
      AS.valueN F α n N i.1 := by
  have hm := (Finset.mem_filter.mp ha).2
  rw [← fa_optimality_rec (AS.toMDC N hN) (fun j => F j.1) α n hn i] at hm
  rw [fa_trunc_action M AS F α n N hN i a] at hm
  simpa [MDC.ApproxSeq.valueN,hN,i.2] using hm

lemma fa_limit_minimizer (M : MDC S Act) (F : S → ℝ≥0) (α : ℝ≥0) (AS : M.ApproxSeq)
    (n : ℕ) (hn : 1 ≤ n) (hFH : AS.FH F α n) (e : ℕ → S → Act)
    (he : ∀ N (hN : AS.N₀ ≤ N) (i : AS.SN N), e N i.1 ∈ AS.minSetN F α n N hN i)
    (f : M.Stationary) (hf : M.IsApproxLimitPoint e f) : ∀ i, f.1 i ∈ M.minSet F α n i := by
  obtain ⟨φ,hφ,heq⟩ := hf
  let B := fa_subsequence M AS φ hφ
  have hconv := (fa_fh_convergence M F α AS n).mpr hFH
  intro i
  have hVN : Tendsto (fun N => B.valueN F α n N i) atTop (𝓝 (M.value F α n i)) := by
    apply ((hconv i).1.comp hφ.tendsto_atTop).congr'
    filter_upwards [eventually_ge_atTop AS.N₀] with N hN
    exact (fa_valueN_subsequence M AS φ hφ F α n N hN i).symm
  have hQN : (fun N => (M.C i (f.1 i) : ℝ≥0∞)+(α : ℝ≥0∞)*
      ∑' j, fa_PN M B N i (f.1 i) j*B.valueN F α (n-1) N j)=ᶠ[atTop]
      (fun N => B.valueN F α n N i) := by
    filter_upwards [eventually_ge_atTop B.N₀,fa_eventually_member M B i,heq i] with N hN hi heqN
    have hNφ : AS.N₀ ≤ φ N := hN.trans (hφ.id_le N)
    have hiφ : i ∈ AS.SN (φ N) := hi.2
    have hm := he (φ N) hNφ ⟨i,hiφ⟩
    rw [heqN] at hm
    have ha : f.1 i ∈ B.minSetN F α n N hN ⟨i,hi.2⟩ := hm
    exact fa_min_actionN M B F α n hn N hN ⟨i,hi.2⟩ (f.1 i) ha
  have hlow := fa_action_lower M B F α (n-1)
    (fun j => fa_liminf_all M B F α (n-1) j) i (f.1 i) (f.2 i)
  rw [liminf_congr hQN,hVN.liminf_eq] at hlow
  have hmin : M.aux F α n i (f.1 i)=M.value F α n i :=
    le_antisymm hlow ((fa_optimality_rec M F α n hn i).le.trans (Finset.inf'_le _ (f.2 i)))
  exact Finset.mem_filter.mpr ⟨f.2 i,hmin.trans (fa_optimality_rec M F α n hn i)⟩

lemma fa_root (M : MDC S Act) (F : S → ℝ≥0) (α : ℝ≥0) (AS : M.ApproxSeq) (n : ℕ) (hn : 1 ≤ n) :
    ((∀ i, Tendsto (fun N => AS.valueN F α n N i) atTop (𝓝 (M.value F α n i)) ∧
        M.value F α n i < ⊤) ↔ AS.FH F α n) ∧
    (AS.FH F α n → ∀ e : ℕ → S → Act, AS.IsStationarySeq e →
      (∀ N (hN : AS.N₀ ≤ N) (i : AS.SN N), e N i.1 ∈ AS.minSetN F α n N hN i) →
      ∀ f : M.Stationary, M.IsApproxLimitPoint e f → ∀ i, f.1 i ∈ M.minSet F α n i) := by
  refine ⟨fa_fh_convergence M F α AS n,?_⟩
  intro hFH e _ he f hf
  exact fa_limit_minimizer M F α AS n hn hFH e he f hf

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
variable {S Act : Type} [Countable S]

lemma fa_valueN_at_rec (M : MDC S Act) (AS : M.ApproxSeq) (F : S → ℝ≥0) (α : ℝ≥0)
    (n N : ℕ) (hN : AS.N₀ ≤ N) (i : S) (hi : i ∈ AS.SN N) :
    AS.valueN F α (n+1) N i=(M.A i).inf' (M.A_nonempty i)
      (fun a => (M.C i a : ℝ≥0∞)+(α : ℝ≥0∞)*
        ∑ j ∈ AS.SN N, AS.PN N i a j*AS.valueN F α n N j) := by
  rw [MDC.ApproxSeq.valueN,dif_pos ⟨hN,hi⟩,
    fa_optimality_rec (AS.toMDC N hN) (fun j => F j.1) α (n+1) (by omega)]
  change (M.A i).inf' (M.A_nonempty i)
    (fun a => (M.C i a : ℝ≥0∞)+(α : ℝ≥0∞)*∑' j : AS.SN N,
      AS.PN N i a j.1*(AS.toMDC N hN).value (fun j => F j.1) α ((n+1)-1) j)= _
  simp only [Nat.add_sub_cancel]
  congr 1
  funext a
  congr 1
  congr 1
  calc
    _ = ∑' j : AS.SN N, AS.PN N i a j.1*AS.valueN F α n N j.1 := by
      apply tsum_congr
      intro j
      simp [MDC.ApproxSeq.valueN,hN,j.2]
    _ = _ := Finset.tsum_subtype (AS.SN N) (fun j : S => AS.PN N i a j*AS.valueN F α n N j)

lemma fa_augmentation_sum (M : MDC S Act) (AS : M.ApproxSeq)
    (q : ℕ → S → Act → S → S → ℝ≥0∞) (hq : AS.IsATASWith q)
    (N : ℕ) (hN : AS.N₀ ≤ N) (i : S) (hi : i ∈ AS.SN N)
    (a : Act) (ha : a ∈ M.A i) (U : S → ℝ≥0∞) :
    (∑ j ∈ AS.SN N, AS.PN N i a j*U j)=
      (∑ j ∈ AS.SN N, M.P i a j*U j)+
        ∑' r : {r : S // r ∉ AS.SN N}, M.P i a r.1*∑ j ∈ AS.SN N, q N i a r.1 j*U j := by
  calc
    _ = ∑ j ∈ AS.SN N, (M.P i a j+
        ∑' r : {r : S // r ∉ AS.SN N}, M.P i a r.1*q N i a r.1 j)*U j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hq.2 N hN i hi a ha j hj]
      rfl
    _ = (∑ j ∈ AS.SN N, M.P i a j*U j)+
        ∑ j ∈ AS.SN N, ∑' r : {r : S // r ∉ AS.SN N}, M.P i a r.1*(q N i a r.1 j*U j) := by
      simp only [add_mul,← ENNReal.tsum_mul_right,Finset.sum_add_distrib,mul_assoc]
    _ = _ := by
      congr 1
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      apply tsum_congr
      intro r
      rw [Finset.mul_sum]

lemma fa_augmentation_sum_le (M : MDC S Act) (AS : M.ApproxSeq)
    (q : ℕ → S → Act → S → S → ℝ≥0∞) (hq : AS.IsATASWith q)
    (N : ℕ) (hN : AS.N₀ ≤ N) (i : S) (hi : i ∈ AS.SN N)
    (a : Act) (ha : a ∈ M.A i) (U : S → ℝ≥0∞)
    (hU : ∀ r, r ∉ AS.SN N → ∑ j ∈ AS.SN N, q N i a r j*U j ≤ U r) :
    (∑ j ∈ AS.SN N, AS.PN N i a j*U j) ≤ ∑' j, M.P i a j*U j := by
  rw [fa_augmentation_sum M AS q hq N hN i hi a ha U]
  calc
    _ ≤ (∑ j ∈ AS.SN N, M.P i a j*U j)+
        ∑' r : {r : S // r ∉ AS.SN N}, M.P i a r.1*U r.1 := by
      apply add_le_add le_rfl
      exact ENNReal.tsum_le_tsum (fun r => mul_le_mul_right (hU r r.2) (M.P i a r))
    _ = _ := ENNReal.sum_add_tsum_compl (AS.SN N) _

lemma fa_augmentation_values_le (M : MDC S Act) (F : S → ℝ≥0) (α : ℝ≥0)
    (AS : M.ApproxSeq) (q : ℕ → S → Act → S → S → ℝ≥0∞) (hq : AS.IsATASWith q)
    (h320 : ∀ n N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, ∀ a ∈ M.A i, ∀ r, r ∉ AS.SN N →
      ∑ j ∈ AS.SN N, q N i a r j*M.value F α n j ≤ M.value F α n r)
    (n N : ℕ) (hN : AS.N₀ ≤ N) (i : S) (hi : i ∈ AS.SN N) :
    AS.valueN F α n N i ≤ M.value F α n i := by
  induction n generalizing i with
  | zero => simp [MDC.ApproxSeq.valueN,hN,hi,fa_value_eq,fa_iter]
  | succ n ih =>
    rw [fa_valueN_at_rec M AS F α n N hN i hi,fa_optimality_rec M F α (n+1) (by omega)]
    apply fa_inf'_mono
    intro a ha
    unfold MDC.aux
    simp only [Nat.add_sub_cancel]
    apply add_le_add le_rfl
    apply mul_le_mul_right
    calc
      _ ≤ ∑ j ∈ AS.SN N, AS.PN N i a j*M.value F α n j :=
        Finset.sum_le_sum (fun j hj => mul_le_mul_right (ih j hj) (AS.PN N i a j))
      _ ≤ _ := fa_augmentation_sum_le M AS q hq N hN i hi a ha _ (h320 n N hN i hi a ha)

lemma fa_fh_of_eventual_upper (M : MDC S Act) (F : S → ℝ≥0) (α : ℝ≥0)
    (AS : M.ApproxSeq) (n : ℕ) (hfin : ∀ i, M.value F α n i < ⊤)
    (hupper : ∀ i, ∀ᶠ N in atTop, AS.valueN F α n N i ≤ M.value F α n i) : AS.FH F α n := by
  intro i
  have hh : limsup (fun N => AS.valueN F α n N i) atTop ≤ M.value F α n i :=
    limsup_le_of_le (by isBoundedDefault) (hupper i)
  exact ⟨hh.trans_lt (hfin i),hh⟩

lemma fa_augmentation_result (M : MDC S Act) (F : S → ℝ≥0) (α : ℝ≥0)
    (hfin : ∀ n, 1 ≤ n → ∀ i, M.value F α n i < ⊤)
    (AS : M.ApproxSeq) (q : ℕ → S → Act → S → S → ℝ≥0∞) (hq : AS.IsATASWith q)
    (h320 : ∀ n N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, ∀ a ∈ M.A i, ∀ r, r ∉ AS.SN N →
      ∑ j ∈ AS.SN N, q N i a r j*M.value F α n j ≤ M.value F α n r) :
    (∀ n, 1 ≤ n → ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, AS.valueN F α n N i ≤ M.value F α n i) ∧
      (∀ n, 1 ≤ n → AS.FH F α n) := by
  refine ⟨fun n _ N hN i hi => fa_augmentation_values_le M F α AS q hq h320 n N hN i hi,?_⟩
  intro n hn
  apply fa_fh_of_eventual_upper M F α AS n (hfin n hn)
  intro i
  filter_upwards [fa_eventually_member M AS i] with N hN
  exact fa_augmentation_values_le M F α AS q hq h320 n N hN.1 i hN.2

end
end SennottDP.FiniteHorizon


namespace SennottDP.FiniteHorizon
open scoped ENNReal NNReal
open Classical Filter Topology
noncomputable section

lemma fa_dominated_tsum {ι : Type*} (f : ℕ → ι → ℝ≥0∞) (g G : ι → ℝ≥0∞)
    (hG : (∑' j, G j) ≠ ⊤) (hbound : ∀ N j, f N j ≤ G j)
    (hlim : ∀ j, Tendsto (fun N => f N j) atTop (𝓝 (g j))) :
    Tendsto (fun N => ∑' j, f N j) atTop (𝓝 (∑' j, g j)) := by
  have hGfin := ENNReal.ne_top_of_tsum_ne_top hG
  have hg (j : ι) : g j ≤ G j := le_of_tendsto (hlim j) (Eventually.of_forall (fun N => hbound N j))
  have hfFin (N : ℕ) (j : ι) : f N j ≠ ⊤ := ne_top_of_le_ne_top (hGfin j) (hbound N j)
  have hgFin (j : ι) : g j ≠ ⊤ := ne_top_of_le_ne_top (hGfin j) (hg j)
  have hsumf (N : ℕ) : (∑' j, f N j) ≠ ⊤ :=
    ne_top_of_le_ne_top hG (ENNReal.tsum_le_tsum (hbound N))
  have hsumg : (∑' j, g j) ≠ ⊤ := ne_top_of_le_ne_top hG (ENNReal.tsum_le_tsum hg)
  apply (ENNReal.tendsto_toReal_iff hsumf hsumg).mp
  have hh := tendsto_tsum_of_dominated_convergence (ENNReal.summable_toReal hG)
    (fun j => (ENNReal.tendsto_toReal (hgFin j)).comp (hlim j))
    (Eventually.of_forall (fun N j => (by
      rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_mono (hGfin j) (hbound N j) : ‖(f N j).toReal‖ ≤ (G j).toReal)))
  simpa only [Function.comp_def,ENNReal.tsum_toReal_eq (hfFin _),ENNReal.tsum_toReal_eq hgFin] using hh

lemma fa_probability_expectation {ι : Type*} (pN : ℕ → ι → ℝ≥0∞) (p : ι → ℝ≥0∞)
    (hpN : ∀ N, (∑' j, pN N j)=1) (hp : (∑' j, p j)=1)
    (hplim : ∀ j, Tendsto (fun N => pN N j) atTop (𝓝 (p j)))
    (wN : ℕ → ι → ℝ≥0∞) (w : ι → ℝ≥0∞) (D : ℝ≥0∞) (hD : D ≠ ⊤)
    (hwN : ∀ N j, wN N j ≤ D) (hwlim : ∀ j, Tendsto (fun N => wN N j) atTop (𝓝 (w j))) :
    Tendsto (fun N => ∑' j, pN N j*wN N j) atTop (𝓝 (∑' j, p j*w j)) := by
  let R := fun N j => min (pN N j) (p j)
  let E := fun N j => pN N j-R N j
  have hpfin (j : ι) : p j ≠ ⊤ :=
    ENNReal.ne_top_of_tsum_ne_top (by rw [hp]; exact ENNReal.one_ne_top) j
  have hw (j : ι) : w j ≤ D := le_of_tendsto (hwlim j) (Eventually.of_forall (fun N => hwN N j))
  have hr (j : ι) : Tendsto (fun N => R N j) atTop (𝓝 (p j)) := by
    simpa [R] using (hplim j).min (tendsto_const_nhds (x := p j))
  have hmass : Tendsto (fun N => ∑' j, R N j) atTop (𝓝 1) := by
    rw [← hp]
    exact fa_dominated_tsum R p p (by rw [hp]; exact ENNReal.one_ne_top)
      (fun N j => min_le_right _ _) hr
  have heq (N : ℕ) : (∑' j, E N j)=1-(∑' j, R N j) := by
    apply ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top
    rw [← ENNReal.tsum_add]
    calc
      _ = ∑' j, pN N j := by
        apply tsum_congr
        intro j
        exact tsub_add_cancel_of_le (min_le_left _ _)
      _ = 1 := hpN N
  have hexcess : Tendsto (fun N => ∑' j, E N j) atTop (𝓝 0) := by
    simp_rw [heq]
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds hmass (Or.inl ENNReal.one_ne_top)
  have hG : (∑' j, p j*D) ≠ ⊤ := by rw [ENNReal.tsum_mul_right,hp,one_mul]; exact hD
  have havg : Tendsto (fun N => ∑' j, R N j*wN N j) atTop (𝓝 (∑' j, p j*w j)) :=
    fa_dominated_tsum _ _ _ hG
      (fun N j => mul_le_mul' (min_le_right _ _) (hwN N j))
      (fun j => ENNReal.Tendsto.mul (hr j) (Or.inr (ne_top_of_le_ne_top hD (hw j)))
        (hwlim j) (Or.inr (hpfin j)))
  have hup : Tendsto (fun N => (∑' j, R N j*wN N j)+D*(∑' j, E N j)) atTop
      (𝓝 (∑' j, p j*w j)) := by
    simpa using havg.add (ENNReal.Tendsto.const_mul hexcess (Or.inr hD))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le havg hup
  · intro N
    exact ENNReal.tsum_le_tsum (fun j => mul_le_mul_left (min_le_left _ _) (wN N j))
  · intro N
    calc
      _ = (∑' j, R N j*wN N j)+(∑' j, E N j*wN N j) := by
        rw [← ENNReal.tsum_add]
        apply tsum_congr
        intro j
        rw [← add_mul,add_tsub_cancel_of_le (min_le_left _ _)]
      _ ≤ (∑' j, R N j*wN N j)+(∑' j, E N j*D) := by
        exact add_le_add le_rfl (ENNReal.tsum_le_tsum (fun j => mul_le_mul_right (hwN N j) (E N j)))
      _ = _ := by
        dsimp only
        rw [ENNReal.tsum_mul_right]
        ring

end
end SennottDP.FiniteHorizon


namespace SennottDP.FiniteHorizon
open scoped ENNReal NNReal
open Classical Filter Topology
noncomputable section
variable {S Act : Type} [Countable S]

lemma fa_excess_weighted_bound (M : MDC S Act) (AS : M.ApproxSeq)
    (q : ℕ → S → Act → S → S → ℝ≥0∞) (hq : AS.IsATASWith q)
    (G : Finset S) (hG : AS.SendsExcessTo q (G : Set S))
    (N : ℕ) (hN : AS.N₀ ≤ N) (i : S) (hi : i ∈ AS.SN N) (a : Act) (ha : a ∈ M.A i)
    (r : S) (hr : r ∉ AS.SN N) (U : S → ℝ≥0∞) (b : ℝ≥0∞) (hb : ∀ j ∈ G, U j ≤ b) :
    (∑ j ∈ AS.SN N, q N i a r j*U j) ≤ b := by
  have hsum := hq.1 N hN i hi a ha r hr
  have hpart : (∑ j ∈ AS.SN N, if j ∈ G then q N i a r j else 0)=1 := by
    rw [← Finset.sum_filter]
    simpa only [Finset.mem_coe] using hG N hN i hi a ha r hr
  have hsupport (j : S) (hj : j ∈ AS.SN N) (hjG : j ∉ G) : q N i a r j=0 := by
    have hh := fa_finset_eq_term (AS.SN N)
      (fun j => if j ∈ G then q N i a r j else 0) (q N i a r)
      (fun j _ => by split_ifs <;> simp)
      (by rw [hpart]; exact ENNReal.one_ne_top) (hpart.trans hsum.symm) j hj
    simpa [hjG] using hh.symm
  calc
    _ ≤ ∑ j ∈ AS.SN N, q N i a r j*b := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hjG : j ∈ G
      · exact mul_le_mul_right (hb j hjG) _
      · simp [hsupport j hj hjG]
    _ = b := by rw [← Finset.sum_mul,hsum,one_mul]

lemma fa_excess_sum_bound (M : MDC S Act) (AS : M.ApproxSeq)
    (q : ℕ → S → Act → S → S → ℝ≥0∞) (hq : AS.IsATASWith q)
    (G : Finset S) (hG : AS.SendsExcessTo q (G : Set S))
    (N : ℕ) (hN : AS.N₀ ≤ N) (i : S) (hi : i ∈ AS.SN N) (a : Act) (ha : a ∈ M.A i)
    (U : S → ℝ≥0∞) (b : ℝ≥0∞) (hb : ∀ j ∈ G, U j ≤ b) :
    (∑ j ∈ AS.SN N, AS.PN N i a j*U j) ≤ (∑' j, M.P i a j*U j)+
      (∑' r : {r : S // r ∉ AS.SN N}, M.P i a r.1)*b := by
  rw [fa_augmentation_sum M AS q hq N hN i hi a ha U]
  apply add_le_add (ENNReal.sum_le_tsum _)
  rw [← ENNReal.tsum_mul_right]
  exact ENNReal.tsum_le_tsum (fun r => mul_le_mul_right
    (fa_excess_weighted_bound M AS q hq G hG N hN i hi a ha r r.2 U b hb) (M.P i a r))

lemma fa_outside_mass_le_one (M : MDC S Act) (AS : M.ApproxSeq) (N : ℕ)
    (i : S) (a : Act) (ha : a ∈ M.A i) :
    (∑' r : {r : S // r ∉ AS.SN N}, M.P i a r.1) ≤ 1 := by
  have hh := ENNReal.sum_add_tsum_compl (AS.SN N) (M.P i a)
  rw [M.P_sum i a ha] at hh
  exact (le_add_self).trans_eq hh

lemma fa_outside_mass_limit (M : MDC S Act) (AS : M.ApproxSeq) (i : S)
    (a : Act) (ha : a ∈ M.A i) :
    Tendsto (fun N => ∑' r : {r : S // r ∉ AS.SN N}, M.P i a r.1) atTop (𝓝 0) := by
  have hh := fa_dominated_tsum (fun N j => if j ∈ AS.SN N then 0 else M.P i a j)
    (fun _ => 0) (M.P i a) (by rw [M.P_sum i a ha]; exact ENNReal.one_ne_top)
    (fun N j => by split_ifs <;> simp) (fun j => (by
      apply tendsto_const_nhds.congr'
      filter_upwards [fa_eventually_member M AS j] with N hN
      simp [hN.2]))
  have he (N : ℕ) : (∑' r : {r : S // r ∉ AS.SN N}, M.P i a r.1)=
      ∑' j, if j ∈ AS.SN N then 0 else M.P i a j := by
    change (∑' r : ({r : S | r ∉ AS.SN N} : Set S), M.P i a r.1)=_
    rw [tsum_subtype ({r : S | r ∉ AS.SN N}) (M.P i a)]
    simp only [Set.indicator_apply,Set.mem_setOf_eq,ite_not]
  simp_rw [he]
  simpa only [tsum_zero] using hh

lemma fa_value_finite_all (M : MDC S Act) (F : S → ℝ≥0) (α : ℝ≥0)
    (hfin : ∀ n, 1 ≤ n → ∀ i, M.value F α n i < ⊤) (n : ℕ) (i : S) :
    M.value F α n i ≠ ⊤ := by
  cases n with
  | zero => rw [fa_value_eq]; exact ENNReal.coe_ne_top
  | succ n => exact ne_of_lt (hfin (n+1) (by omega) i)

def fa_K (M : MDC S Act) (F : S → ℝ≥0) (α : ℝ≥0) (G : Finset S) : ℕ → ℝ≥0∞
  | 0 => 0
  | n+1 => (∑ j ∈ G, M.value F α n j)+fa_K M F α G n

lemma fa_K_finite (M : MDC S Act) (F : S → ℝ≥0) (α : ℝ≥0) (G : Finset S)
    (hfin : ∀ n, 1 ≤ n → ∀ i, M.value F α n i < ⊤) (n : ℕ) : fa_K M F α G n ≠ ⊤ := by
  induction n with
  | zero => exact ENNReal.zero_ne_top
  | succ n ih =>
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.sum_ne_top.mpr (fun j _ => fa_value_finite_all M F α hfin n j),ih⟩

lemma fa_excess_envelope (M : MDC S Act) (F : S → ℝ≥0) (α : ℝ≥0) (hα : α ≤ 1)
    (AS : M.ApproxSeq) (q : ℕ → S → Act → S → S → ℝ≥0∞) (hq : AS.IsATASWith q)
    (G : Finset S) (hG : AS.SendsExcessTo q (G : Set S)) (n N : ℕ) (i : S) :
    AS.valueN F α n N i ≤ M.value F α n i+fa_K M F α G n := by
  by_cases hvalid : AS.N₀ ≤ N ∧ i ∈ AS.SN N
  · induction n generalizing i with
    | zero => simp [MDC.ApproxSeq.valueN,hvalid.1,hvalid.2,fa_value_eq,fa_iter,fa_K]
    | succ n ih =>
      rw [fa_valueN_at_rec M AS F α n N hvalid.1 i hvalid.2]
      obtain ⟨f,hf⟩ := fa_selector M α (M.value F α n)
      let a := f.1 i
      have ha := f.2 i
      have ham : fa_Q M α (M.value F α n) i a=M.value F α (n+1) i := by
        rw [fa_optimality_rec M F α (n+1) (by omega)]
        exact hf i
      refine (Finset.inf'_le _ ha).trans ?_
      have hsum : (∑ j ∈ AS.SN N, AS.PN N i a j*AS.valueN F α n N j) ≤
          (∑' j, M.P i a j*M.value F α n j)+fa_K M F α G (n+1) := by
        calc
          _ ≤ ∑ j ∈ AS.SN N, AS.PN N i a j*(M.value F α n j+fa_K M F α G n) :=
            Finset.sum_le_sum (fun j hj => mul_le_mul_right (ih j ⟨hvalid.1,hj⟩) (AS.PN N i a j))
          _ = (∑ j ∈ AS.SN N, AS.PN N i a j*M.value F α n j)+fa_K M F α G n := by
            simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,AS.PN_sum N hvalid.1 i hvalid.2 a ha,one_mul]
          _ ≤ ((∑' j, M.P i a j*M.value F α n j)+
              (∑' r : {r : S // r ∉ AS.SN N}, M.P i a r.1)*(∑ j ∈ G, M.value F α n j))+fa_K M F α G n :=
            add_le_add (fa_excess_sum_bound M AS q hq G hG N hvalid.1 i hvalid.2 a ha _ _
              (fun j hj => Finset.single_le_sum (fun _ _ => bot_le) hj)) le_rfl
          _ ≤ ((∑' j, M.P i a j*M.value F α n j)+(∑ j ∈ G, M.value F α n j))+fa_K M F α G n := by
            apply add_le_add ?_ le_rfl
            apply add_le_add le_rfl
            simpa only [one_mul] using mul_le_mul_left (fa_outside_mass_le_one M AS N i a ha)
              (∑ j ∈ G, M.value F α n j)
          _ = _ := by simp only [fa_K]; ring
      calc
        _ ≤ (M.C i a : ℝ≥0∞)+(α : ℝ≥0∞)*
            ((∑' j, M.P i a j*M.value F α n j)+fa_K M F α G (n+1)) :=
          add_le_add le_rfl (mul_le_mul_right hsum _)
        _ = fa_Q M α (M.value F α n) i a+(α : ℝ≥0∞)*fa_K M F α G (n+1) := by
          unfold fa_Q
          ring
        _ ≤ M.value F α (n+1) i+fa_K M F α G (n+1) := by
          rw [ham]
          apply add_le_add le_rfl
          simpa only [one_mul] using mul_le_mul_left (show (α : ℝ≥0∞) ≤ 1 by exact_mod_cast hα)
            (fa_K M F α G (n+1))
  · simp [MDC.ApproxSeq.valueN,hvalid]

lemma fa_excess_result (M : MDC S Act) (F : S → ℝ≥0) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hfin : ∀ n, 1 ≤ n → ∀ i, M.value F α n i < ⊤)
    (AS : M.ApproxSeq) (q : ℕ → S → Act → S → S → ℝ≥0∞) (hq : AS.IsATASWith q)
    (G : Finset S) (hG : AS.SendsExcessTo q (G : Set S)) :
    ∀ n, 1 ≤ n → AS.FH F α n := by
  have hconv : ∀ n i, Tendsto (fun N => AS.valueN F α n N i) atTop (𝓝 (M.value F α n i)) := by
    intro n
    induction n with
    | zero => exact fa_valueN_zero M AS F α
    | succ n ih =>
      intro i
      obtain ⟨f,hf⟩ := fa_selector M α (M.value F α n)
      let a := f.1 i
      have ha := f.2 i
      have ham : fa_Q M α (M.value F α n) i a=M.value F α (n+1) i := by
        rw [fa_optimality_rec M F α (n+1) (by omega)]
        exact hf i
      have hαne : (α : ℝ≥0∞) ≠ 0 := by exact_mod_cast ne_of_gt hα0
      have hPV : (∑' j, M.P i a j*M.value F α n j) ≠ ⊤ := by
        intro ht
        have htop : fa_Q M α (M.value F α n) i a=⊤ := by simp [fa_Q,ht,hαne]
        exact (ne_of_lt (hfin (n+1) (by omega) i)) (ham.symm.trans htop)
      have hdom : (∑' j, M.P i a j*(M.value F α n j+fa_K M F α G n)) ≠ ⊤ := by
        rw [show (∑' j, M.P i a j*(M.value F α n j+fa_K M F α G n))=
            (∑' j, M.P i a j*M.value F α n j)+fa_K M F α G n by
          simp only [mul_add,ENNReal.tsum_add,ENNReal.tsum_mul_right,M.P_sum i a ha,one_mul]]
        exact ENNReal.add_ne_top.mpr ⟨hPV,fa_K_finite M F α G hfin n⟩
      have hmean : Tendsto (fun N => ∑' j, M.P i a j*AS.valueN F α n N j) atTop
          (𝓝 (∑' j, M.P i a j*M.value F α n j)) :=
        fa_dominated_tsum _ _ _ hdom
          (fun N j => mul_le_mul_right (fa_excess_envelope M F α hα1 AS q hq G hG n N j) _)
          (fun j => ENNReal.Tendsto.const_mul (ih j) (Or.inr
            (ENNReal.ne_top_of_tsum_ne_top (by rw [M.P_sum i a ha]; exact ENNReal.one_ne_top) j)))
      have hmass : Tendsto (fun N => (∑' r : {r : S // r ∉ AS.SN N}, M.P i a r.1)*
          fa_K M F α G (n+1)) atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.mul_const (fa_outside_mass_limit M AS i a ha)
          (Or.inr (fa_K_finite M F α G hfin (n+1)))
      let upper := fun N => (M.C i a : ℝ≥0∞)+(α : ℝ≥0∞)*
        ((∑' j, M.P i a j*AS.valueN F α n N j)+
          (∑' r : {r : S // r ∉ AS.SN N}, M.P i a r.1)*fa_K M F α G (n+1))
      have hu : Tendsto upper atTop (𝓝 (M.value F α (n+1) i)) := by
        rw [← ham]
        simpa only [upper,fa_Q,add_zero] using tendsto_const_nhds.add
          (ENNReal.Tendsto.const_mul (hmean.add hmass) (Or.inr ENNReal.coe_ne_top))
      have hupper : ∀ᶠ N in atTop, AS.valueN F α (n+1) N i ≤ upper N := by
        filter_upwards [fa_eventually_member M AS i] with N hN
        rw [fa_valueN_at_rec M AS F α n N hN.1 i hN.2]
        refine (Finset.inf'_le _ ha).trans ?_
        apply add_le_add le_rfl
        apply mul_le_mul_right
        apply fa_excess_sum_bound M AS q hq G hG N hN.1 i hN.2 a ha
        intro j hj
        calc
          _ ≤ M.value F α n j+fa_K M F α G n := fa_excess_envelope M F α hα1 AS q hq G hG n N j
          _ ≤ (∑ k ∈ G, M.value F α n k)+fa_K M F α G n :=
            add_le_add (Finset.single_le_sum (fun _ _ => bot_le) hj) le_rfl
      have hsup : limsup (fun N => AS.valueN F α (n+1) N i) atTop ≤ M.value F α (n+1) i := by
        exact (limsup_le_limsup hupper).trans_eq hu.limsup_eq
      exact tendsto_of_le_liminf_of_limsup_le (fa_liminf_all M AS F α (n+1) i) hsup
  intro n hn
  apply (fa_fh_convergence M F α AS n).mp
  exact fun i => ⟨hconv n i,hfin n hn i⟩

end
end SennottDP.FiniteHorizon


namespace SennottDP.DiscountedASM
open scoped ENNReal NNReal
open Classical Filter Topology
open SennottDP.FiniteHorizon
noncomputable section
variable {S Act : Type} [Countable S]

lemma da_ATAS (M : MDC S Act) (Δs : ApproxSeq M)
    (q : ℕ → S → Act → S → S → ℝ≥0∞) (hq : Δs.IsATAS q) : (da_AS M Δs).IsATASWith q := by
  constructor
  · intro N hN i hi a ha r hr
    exact (hq N hN i hi a ha).1 r hr
  · intro N hN i hi a ha j hj
    have he : (∑' r : {r : S // r ∉ Δs.SN N}, M.P i a r.1*q N i a r.1 j)=
        ∑' r : S, if r ∈ Δs.SN N then 0 else M.P i a r*q N i a r j := by
      change (∑' r : ({r : S | r ∉ Δs.SN N} : Set S), M.P i a r.1*q N i a r.1 j)=_
      rw [tsum_subtype ({r : S | r ∉ Δs.SN N}) (fun r => M.P i a r*q N i a r j)]
      simp only [Set.indicator_apply,Set.mem_ofPred_eq,ite_not]
    change Δs.PN N i a j=M.P i a j+∑' r : {r : S // r ∉ Δs.SN N}, M.P i a r.1*q N i a r.1 j
    rw [he]
    exact (hq N hN i hi a ha).2 j hj

lemma da_dc_of_upper (M : MDC S Act) (Δs : ApproxSeq M) (α : ℝ≥0) (hV : ∀ i, M.value α i < ⊤)
    (hupper : ∀ N, Δs.N0 ≤ N → ∀ i ∈ Δs.SN N, Δs.VN α N i ≤ M.value α i) : Δs.DC α := by
  intro i
  have hh : limsup (fun N => Δs.VN α N i) atTop ≤ M.value α i := by
    apply limsup_le_of_le (by isBoundedDefault)
    filter_upwards [fa_eventually_member (da_model M) (da_AS M Δs) i] with N hN
    exact hupper N hN.1 i hN.2
  exact ⟨hh.trans_lt (hV i),hh⟩

lemma da_augmentation_result (M : MDC S Act) (Δs : ApproxSeq M) (α : ℝ≥0)
    (hV : ∀ i, M.value α i < ⊤)
    (q : ℕ → S → Act → S → S → ℝ≥0∞) (hq : Δs.IsATAS q)
    (h320 : ∀ N, Δs.N0 ≤ N → ∀ i ∈ Δs.SN N, ∀ a ∈ M.A i, ∀ r, r ∉ Δs.SN N → ∀ n : ℕ,
      ∑ j ∈ Δs.SN N, q N i a r j * M.horizonValue α n j ≤ M.horizonValue α n r) :
    (∀ N, Δs.N0 ≤ N → ∀ i ∈ Δs.SN N, Δs.VN α N i ≤ M.value α i) ∧ Δs.DC α := by
  have h320' : ∀ n N, (da_AS M Δs).N₀ ≤ N → ∀ i ∈ (da_AS M Δs).SN N,
      ∀ a ∈ (da_model M).A i, ∀ r, r ∉ (da_AS M Δs).SN N →
        ∑ j ∈ (da_AS M Δs).SN N, q N i a r j*(da_model M).value (fun _ => 0) α n j ≤
          (da_model M).value (fun _ => 0) α n r := by
    intro n N hN i hi a ha r hr
    simpa only [da_horizonValue,da_AS] using h320 N hN i hi a ha r hr n
  have hupper : ∀ N, Δs.N0 ≤ N → ∀ i ∈ Δs.SN N, Δs.VN α N i ≤ M.value α i := by
    intro N hN i hi
    rw [ApproxSeq.VN,dif_pos ⟨hN,hi⟩,da_value_eq_limit]
    apply iSup_le
    intro n
    have hh := fa_augmentation_values_le (da_model M) (fun _ => 0) α (da_AS M Δs) q
      (da_ATAS M Δs q hq) h320' n N hN i hi
    rw [da_horizonN M Δs α n N i hN hi,← da_horizonValue M α n i] at hh
    rw [da_horizonValue_eq_iter] at hh
    exact hh.trans (da_horizon_le_value M α n i)
  exact ⟨hupper,da_dc_of_upper M Δs α hV hupper⟩

end
end SennottDP.DiscountedASM


namespace SennottDP.DiscountedASM
open scoped ENNReal NNReal
open Classical Filter Topology
open SennottDP.FiniteHorizon
noncomputable section
variable {S Act : Type} [Countable S]

lemma da_value_le_supersolution (M : MDC S Act) (α : ℝ≥0) (U : S → ℝ≥0∞)
    (hU : ∀ i, fa_T (da_model M) α U i ≤ U i) : ∀ i, M.value α i ≤ U i := by
  obtain ⟨f,hf⟩ := fa_selector (da_model M) α U
  have hc := da_stationary_supersolution M α f.1 f.2 U (fun i => (hf i).le.trans (hU i))
  intro i
  exact (iInf_le _ (M.ofStationary f.1 f.2)).trans (hc i)

lemma da_Q_add_constant (M : MDC S Act) (α : ℝ≥0) (U : S → ℝ≥0∞) (b : ℝ≥0∞)
    (i : S) (a : Act) (ha : a ∈ M.A i) :
    fa_Q (da_model M) α (fun j => U j+b) i a=fa_Q (da_model M) α U i a+(α : ℝ≥0∞)*b := by
  unfold fa_Q
  simp only [da_model,mul_add,ENNReal.tsum_add,ENNReal.tsum_mul_right,M.P_sum i a ha,one_mul]
  ring

lemma da_inf_add {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (U : ι → ℝ≥0∞) (b : ℝ≥0∞) :
    s.inf' hs (fun j => U j+b)=s.inf' hs U+b := by
  apply le_antisymm
  · obtain ⟨j,hj,he⟩ := Finset.exists_mem_eq_inf' hs U
    exact (Finset.inf'_le _ hj).trans_eq (by rw [he])
  · apply Finset.le_inf'
    intro j hj
    exact add_le_add (Finset.inf'_le _ hj) le_rfl

lemma da_T_add_constant (M : MDC S Act) (α : ℝ≥0) (U : S → ℝ≥0∞) (b : ℝ≥0∞) (i : S) :
    fa_T (da_model M) α (fun j => U j+b) i=fa_T (da_model M) α U i+(α : ℝ≥0∞)*b := by
  have he : (M.A i).inf' (M.A_nonempty i) (fa_Q (da_model M) α (fun j => U j+b) i)=
      (M.A i).inf' (M.A_nonempty i) (fun a => fa_Q (da_model M) α U i a+(α : ℝ≥0∞)*b) := by
    apply le_antisymm <;> apply fa_inf'_mono <;> intro a ha
    · exact (da_Q_add_constant M α U b i a ha).le
    · exact (da_Q_add_constant M α U b i a ha).symm.le
  exact he.trans (da_inf_add _ _ _ _)

lemma da_terminal_iter (M : MDC S Act) (α K : ℝ≥0) (n : ℕ) (i : S) :
    fa_iter (da_model M) (fun _ => K) α n i=da_iter M α n i+(α : ℝ≥0∞)^n*(K : ℝ≥0∞) := by
  induction n generalizing i with
  | zero => simp [da_iter,fa_iter]
  | succ n ih =>
    have he : fa_iter (da_model M) (fun _ => K) α n=
        fun j => da_iter M α n j+(α : ℝ≥0∞)^n*(K : ℝ≥0∞) := funext ih
    change fa_T (da_model M) α (fa_iter (da_model M) (fun _ => K) α n) i=_
    rw [he,da_T_add_constant]
    change da_iter M α (n+1) i+(α : ℝ≥0∞)*((α : ℝ≥0∞)^n*(K : ℝ≥0∞))=_
    rw [pow_succ]
    ring

lemma da_value_le_terminal_iter (M : MDC S Act) (α K : ℝ≥0)
    (hK : ∀ i, fa_T (da_model M) α (fun _ => K) i ≤ (K : ℝ≥0∞)) (n : ℕ) (i : S) :
    M.value α i ≤ fa_iter (da_model M) (fun _ => K) α n i := by
  have hsuper (n : ℕ) : ∀ i, fa_T (da_model M) α (fa_iter (da_model M) (fun _ => K) α n) i ≤
      fa_iter (da_model M) (fun _ => K) α n i := by
    induction n with
    | zero => exact hK
    | succ n ih => exact fun i => da_T_mono M α _ _ ih i
  exact da_value_le_supersolution M α _ (hsuper n) i

lemma da_discount_constant (α B : ℝ≥0) (hα : α < 1) :
    ∃ K : ℝ≥0, B+α*K=K := by
  let d := 1-α
  have hd : d ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr hα)
  let K := B/d
  have hb : K*d=B := div_mul_cancel₀ B hd
  refine ⟨K,?_⟩
  calc
    B+α*K=K*d+K*α := by rw [hb]; ring
    _ = K*(d+α) := by ring
    _ = K := by rw [show d+α=1 from tsub_add_cancel_of_le hα.le,mul_one]

lemma da_bounded_subsolution (M : MDC S Act) (α : ℝ≥0) (hα : α < 1)
    (f : S → Act) (hf : ∀ i, f i ∈ M.A i) (U V : S → ℝ≥0∞) (K : ℝ≥0)
    (hfixed : ∀ i, fa_Q (da_model M) α V i (f i)=V i)
    (hU : ∀ i, U i ≤ fa_Q (da_model M) α U i (f i))
    (hbound : ∀ i, U i ≤ V i+(K : ℝ≥0∞)) : ∀ i, U i ≤ V i := by
  have hn (n : ℕ) (i : S) : U i ≤ V i+(α : ℝ≥0∞)^n*(K : ℝ≥0∞) := by
    induction n generalizing i with
    | zero => simpa using hbound i
    | succ n ih =>
      calc
        _ ≤ fa_Q (da_model M) α U i (f i) := hU i
        _ ≤ fa_Q (da_model M) α (fun j => V j+(α : ℝ≥0∞)^n*(K : ℝ≥0∞)) i (f i) :=
          da_Q_mono M α _ _ ih i (f i)
        _ = _ := by rw [da_Q_add_constant M α V _ i (f i) (hf i),hfixed,pow_succ]; ring
  have ht : Tendsto (fun n : ℕ => (α : ℝ≥0∞)^n*(K : ℝ≥0∞)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by exact_mod_cast hα)) (Or.inr ENNReal.coe_ne_top)
  intro i
  have hlim : Tendsto (fun n : ℕ => V i+(α : ℝ≥0∞)^n*(K : ℝ≥0∞)) atTop (𝓝 (V i)) := by
    simpa using tendsto_const_nhds.add ht
  exact ge_of_tendsto hlim (Eventually.of_forall (fun n => hn n i))

end
end SennottDP.DiscountedASM


namespace SennottDP.DiscountedASM
open scoped ENNReal NNReal
open Classical Filter Topology
open SennottDP.FiniteHorizon
noncomputable section
variable {S Act : Type} [Countable S]

lemma da_excess_to (M : MDC S Act) (Δs : ApproxSeq M)
    (q : ℕ → S → Act → S → S → ℝ≥0∞) (G : Finset S) (hG : Δs.SendsExcessTo q G) :
    (da_AS M Δs).SendsExcessTo q (G : Set S) := by
  intro N hN i hi a ha r hr
  simpa only [da_AS,Finset.mem_coe] using hG N hN i hi a ha r hr

lemma da_finite_envelope (M : MDC S Act) (Δs : ApproxSeq M) (α : ℝ≥0) (hα : α < 1)
    (hV : ∀ i, M.value α i < ⊤)
    (q : ℕ → S → Act → S → S → ℝ≥0∞) (hq : Δs.IsATAS q)
    (G : Finset S) (hG : Δs.SendsExcessTo q G) :
    ∃ K : ℝ≥0, ∀ N i, Δs.VN α N i ≤ M.value α i+(K : ℝ≥0∞) := by
  have hsum : (∑ j ∈ G, M.value α j) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun j _ => ne_of_lt (hV j))
  obtain ⟨b,hb⟩ : ∃ b : ℝ≥0, (b : ℝ≥0∞)=∑ j ∈ G, M.value α j :=
    ⟨(∑ j ∈ G, M.value α j).toNNReal,ENNReal.coe_toNNReal hsum⟩
  obtain ⟨K,hK⟩ := da_discount_constant α (α*b) hα
  have hKe : (α : ℝ≥0∞)*((b : ℝ≥0∞)+(K : ℝ≥0∞))=(K : ℝ≥0∞) := by
    exact_mod_cast (show α*(b+K)=K by simpa only [mul_add] using hK)
  obtain ⟨f,hf⟩ := fa_selector (da_model M) α (M.value α)
  have hfixed (i : S) : fa_Q (da_model M) α (M.value α) i (f.1 i)=M.value α i :=
    (hf i).trans (da_value_fixed M α i).symm
  have hbG (j : S) (hj : j ∈ G) : M.value α j ≤ (b : ℝ≥0∞) := by
    rw [hb]
    exact Finset.single_le_sum (fun _ _ => bot_le) hj
  refine ⟨K,?_⟩
  intro N i
  by_cases hvalid : Δs.N0 ≤ N ∧ i ∈ Δs.SN N
  · rw [ApproxSeq.VN,dif_pos hvalid]
    apply da_value_le_supersolution (Δs.truncMDC N hvalid.1) α (fun j => M.value α j.1+(K : ℝ≥0∞))
    intro k
    let a := f.1 k.1
    have ha := f.2 k.1
    refine (Finset.inf'_le _ ha).trans ?_
    change (M.C k.1 a : ℝ≥0∞)+(α : ℝ≥0∞)*
      (∑' j : Δs.SN N, Δs.PN N k.1 a j.1*(M.value α j.1+(K : ℝ≥0∞))) ≤ _
    have hs : (∑' j : Δs.SN N, Δs.PN N k.1 a j.1*(M.value α j.1+(K : ℝ≥0∞))) ≤
        (∑' j, M.P k.1 a j*M.value α j)+(b : ℝ≥0∞)+(K : ℝ≥0∞) := by
      rw [Finset.tsum_subtype (Δs.SN N) (fun j => Δs.PN N k.1 a j*(M.value α j+(K : ℝ≥0∞)))]
      calc
        _ = (∑ j ∈ Δs.SN N, Δs.PN N k.1 a j*M.value α j)+(K : ℝ≥0∞) := by
          simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,
            Δs.PN_sum N hvalid.1 k.1 k.2 a ha,one_mul]
        _ ≤ ((∑' j, M.P k.1 a j*M.value α j)+
            (∑' r : {r : S // r ∉ Δs.SN N}, M.P k.1 a r.1)*(b : ℝ≥0∞))+(K : ℝ≥0∞) := by
          apply add_le_add ?_ le_rfl
          exact fa_excess_sum_bound (da_model M) (da_AS M Δs) q (da_ATAS M Δs q hq)
            G (da_excess_to M Δs q G hG) N hvalid.1 k.1 k.2 a ha (M.value α) b hbG
        _ ≤ _ := by
          apply add_le_add ?_ le_rfl
          apply add_le_add le_rfl
          simpa only [one_mul,da_AS,da_model] using mul_le_mul_left
            (fa_outside_mass_le_one (da_model M) (da_AS M Δs) N k.1 a ha) (b : ℝ≥0∞)
    calc
      _ ≤ (M.C k.1 a : ℝ≥0∞)+(α : ℝ≥0∞)*
          ((∑' j, M.P k.1 a j*M.value α j)+(b : ℝ≥0∞)+(K : ℝ≥0∞)) :=
        add_le_add le_rfl (mul_le_mul_right hs _)
      _ = fa_Q (da_model M) α (M.value α) k.1 a+(α : ℝ≥0∞)*((b : ℝ≥0∞)+(K : ℝ≥0∞)) := by
        unfold fa_Q
        simp only [da_model]
        ring
      _ = _ := by rw [hKe,hfixed]
  · simp [ApproxSeq.VN,hvalid]

end
end SennottDP.DiscountedASM


namespace SennottDP.DiscountedASM
open scoped ENNReal NNReal
open Classical Filter Topology
open SennottDP.FiniteHorizon
noncomputable section

lemma da_tail_antitone (u : ℕ → ℝ≥0∞) : Antitone (fun N => ⨆ k : ℕ, u (k+N)) := by
  intro n m hnm
  apply iSup_le
  intro k
  have he : (k+m-n)+n=k+m := by omega
  exact (congrArg u he).symm.le.trans (le_iSup (fun k => u (k+n)) (k+m-n))

lemma da_tsum_limsup {ι : Type*} (f : ℕ → ι → ℝ≥0∞) (G : ι → ℝ≥0∞)
    (hG : (∑' j, G j) ≠ ⊤) (hbound : ∀ N j, f N j ≤ G j) :
    limsup (fun N => ∑' j, f N j) atTop ≤ ∑' j, limsup (fun N => f N j) atTop := by
  let T := fun N j => ⨆ k : ℕ, f (k+N) j
  have hlim (j : ι) : Tendsto (fun N => T N j) atTop (𝓝 (limsup (fun N => f N j) atTop)) := by
    rw [limsup_eq_iInf_iSup_of_nat']
    exact tendsto_atTop_iInf (da_tail_antitone (fun N => f N j))
  have hsum := fa_dominated_tsum T (fun j => limsup (fun N => f N j) atTop) G hG
    (fun N j => iSup_le (fun k => hbound (k+N) j)) hlim
  have hl (N : ℕ) : (∑' j, f N j) ≤ ∑' j, T N j := by
    apply ENNReal.tsum_le_tsum
    intro j
    simpa only [zero_add] using le_iSup (fun k => f (k+N) j) 0
  exact (limsup_le_limsup (Eventually.of_forall hl)).trans_eq hsum.limsup_eq

lemma da_limsup_add (a : ℝ≥0∞) (u : ℕ → ℝ≥0∞) :
    limsup (fun N => a+u N) atTop=a+limsup u atTop := by
  simp only [limsup_eq_iInf_iSup_of_nat']
  rw [ENNReal.add_iInf]
  apply iInf_congr
  intro n
  rw [ENNReal.add_iSup]

lemma da_limsup_add_le (u v : ℕ → ℝ≥0∞) :
    limsup (fun N => u N+v N) atTop ≤ limsup u atTop+limsup v atTop := by
  have ht (w : ℕ → ℝ≥0∞) : Tendsto (fun N => ⨆ k : ℕ, w (k+N)) atTop (𝓝 (limsup w atTop)) := by
    rw [limsup_eq_iInf_iSup_of_nat']
    exact tendsto_atTop_iInf (da_tail_antitone w)
  have hh := (ht u).add (ht v)
  have he : ∀ᶠ N in atTop, u N+v N ≤ (⨆ k : ℕ, u (k+N))+(⨆ k : ℕ, v (k+N)) := by
    apply Eventually.of_forall
    intro N
    apply add_le_add
    · simpa only [zero_add] using le_iSup (fun k => u (k+N)) 0
    · simpa only [zero_add] using le_iSup (fun k => v (k+N)) 0
  exact (limsup_le_limsup he).trans_eq hh.limsup_eq

end
end SennottDP.DiscountedASM


namespace SennottDP.DiscountedASM
open scoped ENNReal NNReal
open Classical Filter Topology
open SennottDP.FiniteHorizon
noncomputable section
variable {S Act : Type} [Countable S]

lemma da_finite_result (M : MDC S Act) (Δs : ApproxSeq M) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1)
    (hV : ∀ i, M.value α i < ⊤)
    (q : ℕ → S → Act → S → S → ℝ≥0∞) (hq : Δs.IsATAS q)
    (G : Finset S) (hG : Δs.SendsExcessTo q G) : Δs.DC α := by
  obtain ⟨K,hK⟩ := da_finite_envelope M Δs α hα1 hV q hq G hG
  let W := fun i => limsup (fun N => Δs.VN α N i) atTop
  have hW (i : S) : W i ≤ M.value α i+(K : ℝ≥0∞) :=
    limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall (fun N => hK N i))
  obtain ⟨f,hf⟩ := fa_selector (da_model M) α (M.value α)
  have hfixed (i : S) : fa_Q (da_model M) α (M.value α) i (f.1 i)=M.value α i :=
    (hf i).trans (da_value_fixed M α i).symm
  have hsub (i : S) : W i ≤ fa_Q (da_model M) α W i (f.1 i) := by
    let a := f.1 i
    have ha := f.2 i
    have hαne : (α : ℝ≥0∞) ≠ 0 := by exact_mod_cast ne_of_gt hα0
    have hPV : (∑' j, M.P i a j*M.value α j) ≠ ⊤ := by
      intro ht
      have htop : fa_Q (da_model M) α (M.value α) i a=⊤ := by simp [fa_Q,da_model,ht,hαne]
      exact (ne_of_lt (hV i)) ((hfixed i).symm.trans htop)
    have hdom : (∑' j, M.P i a j*(M.value α j+(K : ℝ≥0∞))) ≠ ⊤ := by
      simp only [mul_add,ENNReal.tsum_add,ENNReal.tsum_mul_right,M.P_sum i a ha,one_mul]
      exact ENNReal.add_ne_top.mpr ⟨hPV,ENNReal.coe_ne_top⟩
    have hs : limsup (fun N => ∑' j, M.P i a j*Δs.VN α N j) atTop ≤ ∑' j, M.P i a j*W j := by
      have hh := da_tsum_limsup (fun N j => M.P i a j*Δs.VN α N j)
        (fun j => M.P i a j*(M.value α j+(K : ℝ≥0∞))) hdom
        (fun N j => mul_le_mul_right (hK N j) _)
      have he : (fun j => limsup (fun N => M.P i a j*Δs.VN α N j) atTop)=fun j => M.P i a j*W j := by
        funext j
        exact ENNReal.limsup_const_mul_of_ne_top
          (ENNReal.ne_top_of_tsum_ne_top (by rw [M.P_sum i a ha]; exact ENNReal.one_ne_top) j)
      rw [he] at hh
      exact hh
    let b := (∑ j ∈ G, M.value α j)+(K : ℝ≥0∞)
    have hb : b ≠ ⊤ := ENNReal.add_ne_top.mpr
      ⟨ENNReal.sum_ne_top.mpr (fun j _ => ne_of_lt (hV j)),ENNReal.coe_ne_top⟩
    have hmass : Tendsto (fun N => (∑' r : {r : S // r ∉ Δs.SN N}, M.P i a r.1)*b)
        atTop (𝓝 0) := by
      simpa only [da_model,da_AS,zero_mul] using ENNReal.Tendsto.mul_const
        (fa_outside_mass_limit (da_model M) (da_AS M Δs) i a ha) (Or.inr hb)
    let upper := fun N => (M.C i a : ℝ≥0∞)+(α : ℝ≥0∞)*
      ((∑' j, M.P i a j*Δs.VN α N j)+(∑' r : {r : S // r ∉ Δs.SN N}, M.P i a r.1)*b)
    have hupper : ∀ᶠ N in atTop, Δs.VN α N i ≤ upper N := by
      filter_upwards [fa_eventually_member (da_model M) (da_AS M Δs) i] with N hN
      change Δs.N0 ≤ N ∧ i ∈ Δs.SN N at hN
      rw [da_VN_at_rec M Δs α N hN.1 i hN.2]
      refine (Finset.inf'_le _ ha).trans ?_
      rw [da_actionN_sum]
      apply add_le_add le_rfl
      apply mul_le_mul_right
      have hbg (j : S) (hj : j ∈ G) : Δs.VN α N j ≤ b :=
        (hK N j).trans (add_le_add (Finset.single_le_sum (fun _ _ => bot_le) hj) le_rfl)
      simpa only [da_model,da_AS] using
        fa_excess_sum_bound (da_model M) (da_AS M Δs) q (da_ATAS M Δs q hq)
          G (da_excess_to M Δs q G hG) N hN.1 i hN.2 a ha (Δs.VN α N) b hbg
    have hl : W i ≤ limsup upper atTop := limsup_le_limsup hupper
    have he : limsup upper atTop=(M.C i a : ℝ≥0∞)+(α : ℝ≥0∞)*
        limsup (fun N => (∑' j, M.P i a j*Δs.VN α N j)+
          (∑' r : {r : S // r ∉ Δs.SN N}, M.P i a r.1)*b) atTop := by
      unfold upper
      rw [da_limsup_add,ENNReal.limsup_const_mul_of_ne_top ENNReal.coe_ne_top]
    rw [he] at hl
    have hsum := da_limsup_add_le (fun N => ∑' j, M.P i a j*Δs.VN α N j)
      (fun N => (∑' r : {r : S // r ∉ Δs.SN N}, M.P i a r.1)*b)
    rw [hmass.limsup_eq,add_zero] at hsum
    exact hl.trans (add_le_add le_rfl (mul_le_mul_right (hsum.trans hs) _))
  have hfinal := da_bounded_subsolution M α hα1 f.1 f.2 W (M.value α) K hfixed hsub hW
  intro i
  exact ⟨(hfinal i).trans_lt (hV i),hfinal i⟩

end
end SennottDP.DiscountedASM


namespace SennottDP.FiniteHorizon
open scoped ENNReal NNReal
open Classical Filter Topology
noncomputable section
variable {S Act : Type} [Countable S]

def fa_B (B : ℝ≥0) : ℕ → ℝ≥0
  | 0 => B
  | n+1 => B+fa_B B n

lemma fa_bounded_value (M : MDC S Act) (F : S → ℝ≥0) (α B : ℝ≥0) (hα : α ≤ 1)
    (hC : ∀ i, ∀ a ∈ M.A i, M.C i a ≤ B) (hF : ∀ i, F i ≤ B) (n : ℕ) (i : S) :
    M.value F α n i ≤ (fa_B B n : ℝ≥0∞) := by
  rw [fa_value_eq]
  induction n generalizing i with
  | zero =>
    change (F i : ℝ≥0∞) ≤ (B : ℝ≥0∞)
    exact_mod_cast hF i
  | succ n ih =>
    obtain ⟨a,ha⟩ := M.A_nonempty i
    change (M.A i).inf' (M.A_nonempty i) (fa_Q M α (fa_iter M F α n) i) ≤ _
    refine (Finset.inf'_le _ ha).trans ?_
    unfold fa_Q
    have hs : (∑' j, M.P i a j*fa_iter M F α n j) ≤ (fa_B B n : ℝ≥0∞) := by
      calc
        _ ≤ ∑' j, M.P i a j*(fa_B B n : ℝ≥0∞) :=
          ENNReal.tsum_le_tsum (fun j => mul_le_mul_right (ih j) (M.P i a j))
        _ = _ := by rw [ENNReal.tsum_mul_right,M.P_sum i a ha,one_mul]
    change _ ≤ ((B+fa_B B n : ℝ≥0) : ℝ≥0∞)
    rw [ENNReal.coe_add]
    apply add_le_add (by exact_mod_cast hC i a ha)
    calc
      _ ≤ (α : ℝ≥0∞)*(fa_B B n : ℝ≥0∞) := mul_le_mul_right hs _
      _ ≤ 1*(fa_B B n : ℝ≥0∞) := mul_le_mul_left (by exact_mod_cast hα) _
      _ = _ := one_mul _

lemma fa_bounded_valueN (M : MDC S Act) (AS : M.ApproxSeq) (F : S → ℝ≥0)
    (α B : ℝ≥0) (hα : α ≤ 1) (hC : ∀ i, ∀ a ∈ M.A i, M.C i a ≤ B)
    (hF : ∀ i, F i ≤ B) (n N : ℕ) (i : S) : AS.valueN F α n N i ≤ (fa_B B n : ℝ≥0∞) := by
  unfold MDC.ApproxSeq.valueN
  split_ifs with h
  · exact fa_bounded_value (AS.toMDC N h.1) (fun j => F j.1) α B hα
      (fun j a ha => hC j.1 a ha) (fun j => hF j.1) n ⟨i,h.2⟩
  · exact bot_le

def fa_normalizedPN (M : MDC S Act) (AS : M.ApproxSeq) (N : ℕ) (i : S) (a : Act) : S → ℝ≥0∞ :=
  if AS.N₀ ≤ N ∧ i ∈ AS.SN N then fa_PN M AS N i a else M.P i a

lemma fa_normalizedPN_sum (M : MDC S Act) (AS : M.ApproxSeq) (N : ℕ) (i : S)
    (a : Act) (ha : a ∈ M.A i) : (∑' j, fa_normalizedPN M AS N i a j)=1 := by
  unfold fa_normalizedPN
  split_ifs with h
  · exact fa_PN_sum M AS N h.1 i h.2 a ha
  · exact M.P_sum i a ha

lemma fa_normalizedPN_limit (M : MDC S Act) (AS : M.ApproxSeq) (i : S)
    (a : Act) (ha : a ∈ M.A i) (j : S) :
    Tendsto (fun N => fa_normalizedPN M AS N i a j) atTop (𝓝 (M.P i a j)) := by
  apply (fa_PN_tendsto M AS i a ha j).congr'
  filter_upwards [fa_eventually_member M AS i] with N hN
  simp [fa_normalizedPN,hN]

lemma fa_bounded_convergence (M : MDC S Act) (AS : M.ApproxSeq) (F : S → ℝ≥0)
    (α B : ℝ≥0) (hα : α ≤ 1) (hC : ∀ i, ∀ a ∈ M.A i, M.C i a ≤ B)
    (hF : ∀ i, F i ≤ B) (n : ℕ) (i : S) :
    Tendsto (fun N => AS.valueN F α n N i) atTop (𝓝 (M.value F α n i)) := by
  induction n generalizing i with
  | zero => exact fa_valueN_zero M AS F α i
  | succ n ih =>
    have hact (a : Act) (ha : a ∈ M.A i) :
        Tendsto (fun N => (M.C i a : ℝ≥0∞)+(α : ℝ≥0∞)*
          ∑' j, fa_PN M AS N i a j*AS.valueN F α n N j) atTop (𝓝 (M.aux F α (n+1) i a)) := by
      have hs := fa_probability_expectation (fun N => fa_normalizedPN M AS N i a)
        (M.P i a) (fun N => fa_normalizedPN_sum M AS N i a ha) (M.P_sum i a ha)
        (fa_normalizedPN_limit M AS i a ha) (fun N j => AS.valueN F α n N j)
        (M.value F α n) (fa_B B n) ENNReal.coe_ne_top
        (fun N j => fa_bounded_valueN M AS F α B hα hC hF n N j) ih
      have hs' : Tendsto (fun N => ∑' j, fa_PN M AS N i a j*AS.valueN F α n N j) atTop
          (𝓝 (∑' j, M.P i a j*M.value F α n j)) := by
        apply hs.congr'
        filter_upwards [fa_eventually_member M AS i] with N hN
        simp [fa_normalizedPN,hN]
      simpa [MDC.aux] using tendsto_const_nhds.add
        (ENNReal.Tendsto.const_mul hs' (Or.inr ENNReal.coe_ne_top))
    have hh := Filter.Tendsto.finset_inf'_nhds_apply (M.A_nonempty i) hact
    rw [← fa_optimality_rec M F α (n+1) (by omega) i] at hh
    exact hh.congr' ((fa_valueN_rec M AS F α n i).mono (fun _ he => he.symm))

lemma fa_bounded_result (M : MDC S Act) (F : S → ℝ≥0) (AS : M.ApproxSeq)
    (B : ℝ≥0) (hC : ∀ i, ∀ a ∈ M.A i, M.C i a ≤ B) (hF : ∀ i, F i ≤ B) :
    ∀ α : ℝ≥0, 0 < α → α ≤ 1 → ∀ n, 1 ≤ n → AS.FH F α n := by
  intro α _ hα n _
  apply (fa_fh_convergence M F α AS n).mp
  intro i
  exact ⟨fa_bounded_convergence M AS F α B hα hC hF n i,
    (fa_bounded_value M F α B hα hC hF n i).trans_lt ENNReal.coe_lt_top⟩

end
end SennottDP.FiniteHorizon


namespace SennottDP.DiscountedASM
open scoped ENNReal NNReal
open Classical Filter Topology
open SennottDP.FiniteHorizon
noncomputable section
variable {S Act : Type} [Countable S]

lemma da_constant_super (M : MDC S Act) (α B K : ℝ≥0)
    (hC : ∀ i, ∀ a ∈ M.A i, M.C i a ≤ B) (he : B+α*K=K) (i : S) :
    fa_T (da_model M) α (fun _ => K) i ≤ (K : ℝ≥0∞) := by
  obtain ⟨a,ha⟩ := M.A_nonempty i
  refine (Finset.inf'_le _ ha).trans ?_
  change (M.C i a : ℝ≥0∞)+(α : ℝ≥0∞)*(∑' j, M.P i a j*(K : ℝ≥0∞)) ≤ _
  rw [ENNReal.tsum_mul_right,M.P_sum i a ha,one_mul]
  calc
    _ ≤ (B : ℝ≥0∞)+(α : ℝ≥0∞)*(K : ℝ≥0∞) := add_le_add (by exact_mod_cast hC i a ha) le_rfl
    _ = (K : ℝ≥0∞) := by exact_mod_cast he

lemma da_bounded_result (M : MDC S Act) (Δs : ApproxSeq M) (α : ℝ≥0) (hα : α < 1)
    (hB : ∃ B : ℝ≥0, ∀ i, ∀ a ∈ M.A i, M.C i a ≤ B) : Δs.DC α := by
  obtain ⟨B,hC⟩ := hB
  obtain ⟨K,hK⟩ := da_discount_constant α B hα
  have hV (i : S) : M.value α i ≤ (K : ℝ≥0∞) :=
    da_value_le_supersolution M α _ (da_constant_super M α B K hC hK) i
  have hupper (n : ℕ) (i : S) : limsup (fun N => Δs.VN α N i) atTop ≤
      M.value α i+(α : ℝ≥0∞)^n*(K : ℝ≥0∞) := by
    have hconv : Tendsto (fun N => (da_AS M Δs).valueN (fun _ => K) α n N i) atTop
        (𝓝 ((da_model M).value (fun _ => K) α n i)) :=
      fa_bounded_convergence (da_model M) (da_AS M Δs) (fun _ => K) α (B+K) hα.le
        (fun j a ha => (hC j a ha).trans le_self_add) (fun _ => le_add_self) n i
    have hcomp : ∀ᶠ N in atTop, Δs.VN α N i ≤ (da_AS M Δs).valueN (fun _ => K) α n N i := by
      filter_upwards [fa_eventually_member (da_model M) (da_AS M Δs) i] with N hN
      change Δs.N0 ≤ N ∧ i ∈ Δs.SN N at hN
      rw [ApproxSeq.VN,dif_pos hN]
      have hh := da_value_le_terminal_iter (Δs.truncMDC N hN.1) α K
        (da_constant_super (Δs.truncMDC N hN.1) α B K (fun j a ha => hC j.1 a ha) hK) n ⟨i,hN.2⟩
      simpa [SennottDP.FiniteHorizon.MDC.ApproxSeq.valueN,da_AS,hN.1,hN.2,da_model,ApproxSeq.truncMDC,
        SennottDP.FiniteHorizon.MDC.ApproxSeq.toMDC,fa_value_eq] using hh
    calc
      _ ≤ (da_model M).value (fun _ => K) α n i := (limsup_le_limsup hcomp).trans_eq hconv.limsup_eq
      _ = da_iter M α n i+(α : ℝ≥0∞)^n*(K : ℝ≥0∞) := by rw [fa_value_eq,da_terminal_iter]
      _ ≤ _ := add_le_add (by rw [da_value_eq_limit]; exact le_iSup (fun n => da_iter M α n i) n) le_rfl
  have ht : Tendsto (fun n : ℕ => (α : ℝ≥0∞)^n*(K : ℝ≥0∞)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by exact_mod_cast hα)) (Or.inr ENNReal.coe_ne_top)
  intro i
  have hlim : Tendsto (fun n : ℕ => M.value α i+(α : ℝ≥0∞)^n*(K : ℝ≥0∞)) atTop (𝓝 (M.value α i)) := by
    simpa using tendsto_const_nhds.add ht
  have hh := ge_of_tendsto hlim (Eventually.of_forall (fun n => hupper n i))
  exact ⟨hh.trans_lt ((hV i).trans_lt ENNReal.coe_lt_top),hh⟩

end
end SennottDP.DiscountedASM


namespace SennottDP.DiscountedASM
open scoped ENNReal NNReal
open Classical Filter Topology
open SennottDP.FiniteHorizon
noncomputable section
variable {S Act : Type} [Countable S]

lemma da_finite_state_value (M : MDC S Act) [Fintype S] (α : ℝ≥0) (hα : α < 1) (i : S) :
    M.value α i < ⊤ := by
  let B : ℝ≥0 := ∑ j : S, ∑ a ∈ M.A j, M.C j a
  have hC (j : S) (a : Act) (ha : a ∈ M.A j) : M.C j a ≤ B :=
    (Finset.single_le_sum (fun _ _ => bot_le) ha).trans
      (Finset.single_le_sum (f := fun j : S => ∑ a ∈ M.A j, M.C j a) (fun _ _ => bot_le) (Finset.mem_univ j))
  obtain ⟨K,hK⟩ := da_discount_constant α B hα
  exact (da_value_le_supersolution M α _ (da_constant_super M α B K hC hK) i).trans_lt ENNReal.coe_lt_top

lemma da_singleton_prob {ι : Type*} (s : Finset ι) (z : ι) (hz : z ∈ s)
    (q : ι → ℝ≥0∞) (hsum : ∑ j ∈ s, q j=1) (hqz : q z=1) (j : ι) (hj : j ∈ s) :
    q j=if j=z then 1 else 0 := by
  have hF : (∑ k ∈ s, if k=z then (1 : ℝ≥0∞) else 0)=1 := by simp [hz]
  have hh := fa_finset_eq_term s (fun k => if k=z then (1 : ℝ≥0∞) else 0) q
    (fun k _ => by
      split_ifs with he
      · subst k; rw [hqz]
      · exact bot_le)
    (by rw [hF]; exact ENNReal.one_ne_top) (hF.trans hsum.symm) j hj
  exact hh.symm

lemma da_PN_outside_z (M : MDC S Act) (Δs : ApproxSeq M)
    (q : ℕ → S → Act → S → S → ℝ≥0∞) (hq : Δs.IsATAS q) (z : S)
    (hz : ∀ N, Δs.N0 ≤ N → z ∈ Δs.SN N) (hqz : Δs.SendsExcessTo q {z})
    (N : ℕ) (hN : Δs.N0 ≤ N) (i : S) (hi : i ∈ Δs.SN N)
    (a : Act) (ha : a ∈ M.A i) (j : S) (hj : j ∈ Δs.SN N) (hjz : j ≠ z) :
    Δs.PN N i a j=M.P i a j := by
  have hqj (r : S) (hr : r ∉ Δs.SN N) : q N i a r j=0 := by
    have hfilter : (Δs.SN N).filter (· ∈ ({z} : Finset S))={z} := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_singleton]
      constructor
      · exact And.right
      · intro he; subst j; exact ⟨hz N hN,rfl⟩
    have hqzone : q N i a r z=1 := by
      have hh := hqz N hN i hi a ha r hr
      rw [hfilter,Finset.sum_singleton] at hh
      exact hh
    simpa [hjz] using da_singleton_prob (Δs.SN N) z (hz N hN) (q N i a r)
      ((hq N hN i hi a ha).1 r hr) hqzone j hj
  rw [(hq N hN i hi a ha).2 j hj]
  have he : (∑' r : S, if r ∈ Δs.SN N then 0 else M.P i a r*q N i a r j)=0 := by
    apply ENNReal.tsum_eq_zero.mpr
    intro r
    by_cases hr : r ∈ Δs.SN N
    · simp [hr]
    · simp [hr,hqj r hr]
  rw [he,add_zero]

lemma da_toReal_inf {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (U : ι → ℝ≥0∞)
    (hU : ∀ j ∈ s, U j ≠ ⊤) : (s.inf' hs U).toReal=s.inf' hs (fun j => (U j).toReal) := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro j hj
    exact ENNReal.toReal_mono (hU j hj) (Finset.inf'_le _ hj)
  · obtain ⟨j,hj,he⟩ := Finset.exists_mem_eq_inf' hs U
    exact (Finset.inf'_le _ hj).trans_eq (congrArg ENNReal.toReal he.symm)

lemma da_actionN_finite (M : MDC S Act) (Δs : ApproxSeq M) (α : ℝ≥0) (hα : α < 1)
    (N : ℕ) (hN : Δs.N0 ≤ N) (i : S) (hi : i ∈ Δs.SN N) (a : Act) (ha : a ∈ M.A i) :
    da_actionN M Δs α N i a ≠ ⊤ := by
  rw [da_actionN_sum]
  apply ENNReal.add_ne_top.mpr
  refine ⟨ENNReal.coe_ne_top,ENNReal.mul_ne_top ENNReal.coe_ne_top ?_⟩
  apply ENNReal.sum_ne_top.mpr
  intro j hj
  apply ENNReal.mul_ne_top
  · exact ne_top_of_le_ne_top ENNReal.one_ne_top
      ((Finset.single_le_sum (fun _ _ => bot_le) hj).trans_eq (Δs.PN_sum N hN i hi a ha))
  · rw [ApproxSeq.VN,dif_pos ⟨hN,hj⟩]
    exact ne_of_lt (da_finite_state_value (Δs.truncMDC N hN) α hα ⟨j,hj⟩)

lemma da_VN_finite_good (M : MDC S Act) (Δs : ApproxSeq M) (α : ℝ≥0) (hα : α < 1)
    (N : ℕ) (hN : Δs.N0 ≤ N) (j : S) (hj : j ∈ Δs.SN N) : Δs.VN α N j < ⊤ := by
  rw [ApproxSeq.VN,dif_pos ⟨hN,hj⟩]
  exact da_finite_state_value (Δs.truncMDC N hN) α hα ⟨j,hj⟩

lemma da_PN_ne_top (M : MDC S Act) (Δs : ApproxSeq M) (N : ℕ) (hN : Δs.N0 ≤ N)
    (i : S) (hi : i ∈ Δs.SN N) (a : Act) (ha : a ∈ M.A i) (j : S) (hj : j ∈ Δs.SN N) :
    Δs.PN N i a j ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
      ((Finset.single_le_sum (fun _ _ => bot_le) hj).trans_eq (Δs.PN_sum N hN i hi a ha))

lemma da_actionN_toReal (M : MDC S Act) (Δs : ApproxSeq M) (α : ℝ≥0) (hα : α < 1)
    (N : ℕ) (hN : Δs.N0 ≤ N) (i : S) (hi : i ∈ Δs.SN N) (a : Act) (ha : a ∈ M.A i) :
    (da_actionN M Δs α N i a).toReal=(M.C i a : ℝ)+(α : ℝ)*
      ∑ j ∈ Δs.SN N, (Δs.PN N i a j).toReal*(Δs.VN α N j).toReal := by
  have hterm (j : S) (hj : j ∈ Δs.SN N) : Δs.PN N i a j*Δs.VN α N j ≠ ⊤ :=
    ENNReal.mul_ne_top (da_PN_ne_top M Δs N hN i hi a ha j hj)
      (ne_of_lt (da_VN_finite_good M Δs α hα N hN j hj))
  rw [da_actionN_sum,ENNReal.toReal_add ENNReal.coe_ne_top
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.sum_ne_top.mpr hterm))]
  rw [ENNReal.toReal_mul,ENNReal.toReal_sum hterm]
  simp only [ENNReal.coe_toReal,ENNReal.toReal_mul]

lemma da_real_inf_congr {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (U V : ι → ℝ)
    (h : ∀ j ∈ s, U j=V j) : s.inf' hs U=s.inf' hs V := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro j hj
    exact (Finset.inf'_le _ hj).trans_eq (h j hj)
  · apply Finset.le_inf'
    intro j hj
    exact (Finset.inf'_le _ hj).trans_eq (h j hj).symm

lemma da_real_inf_add {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (U : ι → ℝ) (b : ℝ) :
    s.inf' hs (fun j => b+U j)=b+s.inf' hs U := by
  apply le_antisymm
  · obtain ⟨j,hj,he⟩ := Finset.exists_mem_eq_inf' hs U
    exact (Finset.inf'_le _ hj).trans_eq (by rw [he])
  · apply Finset.le_inf'
    intro j hj
    exact add_le_add le_rfl (Finset.inf'_le _ hj)

lemma da_VN_real_rec (M : MDC S Act) (Δs : ApproxSeq M) (α : ℝ≥0) (hα : α < 1)
    (N : ℕ) (hN : Δs.N0 ≤ N) (i : S) (hi : i ∈ Δs.SN N) :
    (Δs.VN α N i).toReal=(M.A i).inf' (M.A_nonempty i)
      (fun a => (M.C i a : ℝ)+(α : ℝ)*∑ j ∈ Δs.SN N,
        (Δs.PN N i a j).toReal*(Δs.VN α N j).toReal) := by
  rw [da_VN_at_rec M Δs α N hN i hi,da_toReal_inf (M.A i) (M.A_nonempty i)
    (da_actionN M Δs α N i) (fun a ha => da_actionN_finite M Δs α hα N hN i hi a ha)]
  exact da_real_inf_congr _ _ _ _ (fun a ha => da_actionN_toReal M Δs α hα N hN i hi a ha)

lemma da_relative_equation (M : MDC S Act) (Δs : ApproxSeq M) (α : ℝ≥0) (hα : α < 1)
    (q : ℕ → S → Act → S → S → ℝ≥0∞) (hq : Δs.IsATAS q) (z : S)
    (hz : ∀ N, Δs.N0 ≤ N → z ∈ Δs.SN N) (hqz : Δs.SendsExcessTo q {z})
    (N : ℕ) (hN : Δs.N0 ≤ N) (i : S) (hi : i ∈ Δs.SN N) :
    (Δs.VN α N i).toReal=(α : ℝ)*(Δs.VN α N z).toReal+
      (M.A i).inf' (M.A_nonempty i) (fun a => (M.C i a : ℝ)+(α : ℝ)*∑ j ∈ Δs.SN N,
        (M.P i a j).toReal*((Δs.VN α N j).toReal-(Δs.VN α N z).toReal)) := by
  have he (a : Act) (ha : a ∈ M.A i) : (M.C i a : ℝ)+(α : ℝ)*
      (∑ j ∈ Δs.SN N, (Δs.PN N i a j).toReal*(Δs.VN α N j).toReal)=
      (α : ℝ)*(Δs.VN α N z).toReal+
        ((M.C i a : ℝ)+(α : ℝ)*∑ j ∈ Δs.SN N,
          (M.P i a j).toReal*((Δs.VN α N j).toReal-(Δs.VN α N z).toReal)) := by
    have hnorm : (∑ j ∈ Δs.SN N, (Δs.PN N i a j).toReal)=1 := by
      rw [← ENNReal.toReal_sum (fun j hj => da_PN_ne_top M Δs N hN i hi a ha j hj),Δs.PN_sum N hN i hi a ha]
      rfl
    have hrel : (∑ j ∈ Δs.SN N, (Δs.PN N i a j).toReal*
        ((Δs.VN α N j).toReal-(Δs.VN α N z).toReal))=
        ∑ j ∈ Δs.SN N, (M.P i a j).toReal*((Δs.VN α N j).toReal-(Δs.VN α N z).toReal) := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hjz : j=z
      · subst j; simp
      · rw [da_PN_outside_z M Δs q hq z hz hqz N hN i hi a ha j hj hjz]
    have hs : (∑ j ∈ Δs.SN N, (Δs.PN N i a j).toReal*(Δs.VN α N j).toReal)=
        (∑ j ∈ Δs.SN N, (M.P i a j).toReal*
          ((Δs.VN α N j).toReal-(Δs.VN α N z).toReal))+(Δs.VN α N z).toReal := by
      calc
        _ = ∑ j ∈ Δs.SN N, ((Δs.PN N i a j).toReal*
            ((Δs.VN α N j).toReal-(Δs.VN α N z).toReal)+
              (Δs.PN N i a j).toReal*(Δs.VN α N z).toReal) := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := by rw [Finset.sum_add_distrib,hrel,← Finset.sum_mul,hnorm,one_mul]
    rw [hs]
    ring
  rw [da_VN_real_rec M Δs α hα N hN i hi]
  calc
    _ = (M.A i).inf' (M.A_nonempty i) (fun a => (α : ℝ)*(Δs.VN α N z).toReal+
        ((M.C i a : ℝ)+(α : ℝ)*∑ j ∈ Δs.SN N,
          (M.P i a j).toReal*((Δs.VN α N j).toReal-(Δs.VN α N z).toReal))) :=
      da_real_inf_congr _ _ _ _ he
    _ = _ := da_real_inf_add _ _ _ _

lemma da_relative_result (M : MDC S Act) (Δs : ApproxSeq M) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1)
    (hV : ∀ i, M.value α i < ⊤)
    (q : ℕ → S → Act → S → S → ℝ≥0∞) (hq : Δs.IsATAS q)
    (z : S) (hz : ∀ N, Δs.N0 ≤ N → z ∈ Δs.SN N) (hqz : Δs.SendsExcessTo q {z}) :
    Δs.DC α ∧
    ∀ N, Δs.N0 ≤ N → (∀ j ∈ Δs.SN N, Δs.VN α N j < ⊤) ∧
      ∀ i ∈ Δs.SN N,
        (Δs.VN α N i).toReal=(α : ℝ)*(Δs.VN α N z).toReal+
          (M.A i).inf' (M.A_nonempty i) (fun a => (M.C i a : ℝ)+(α : ℝ)*∑ j ∈ Δs.SN N,
            (M.P i a j).toReal*((Δs.VN α N j).toReal-(Δs.VN α N z).toReal)) := by
  refine ⟨da_finite_result M Δs α hα0 hα1 hV q hq {z} hqz,?_⟩
  intro N hN
  exact ⟨fun j hj => da_VN_finite_good M Δs α hα1 N hN j hj,
    fun i hi => da_relative_equation M Δs α hα1 q hq z hz hqz N hN i hi⟩

end
end SennottDP.DiscountedASM

open SennottDP.DiscountedASM

/-- Corollary 4.7.5 (pp. 80–81): if `V_α < ∞` and `(Δ_N)` is an ATAS sending the excess
probability to a distinguished state `z` (with `z ∈ S_N` for `N ≥ N₀`), then DC(α) holds, and,
with the relative value function `R^N_α = V^N_α - V^N_α(z)` (the `V^N_α` being finite), the
discount optimality equation of `Δ_N` is
`V^N_α(i) = α V^N_α(z) + min_a {C(i,a) + α Σ_{j ∈ S_N} P_{ij}(a) R^N_α(j)}`, `i ∈ S_N` (4.53). -/
theorem solution {S Act : Type} [Countable S] (M : MDC S Act)
    (Δs : ApproxSeq M) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1)
    (hV : ∀ i, M.value α i < ⊤)
    (q : ℕ → S → Act → S → S → ℝ≥0∞) (hq : Δs.IsATAS q)
    (z : S) (hz : ∀ N, Δs.N0 ≤ N → z ∈ Δs.SN N) (hqz : Δs.SendsExcessTo q {z}) :
    Δs.DC α ∧
    ∀ N, Δs.N0 ≤ N → (∀ j ∈ Δs.SN N, Δs.VN α N j < ⊤) ∧
      ∀ i ∈ Δs.SN N,
        (Δs.VN α N i).toReal =
          (α : ℝ) * (Δs.VN α N z).toReal +
            (M.A i).inf' (M.A_nonempty i) (fun a => (M.C i a : ℝ) +
              (α : ℝ) * ∑ j ∈ Δs.SN N,
                (M.P i a j).toReal * ((Δs.VN α N j).toReal - (Δs.VN α N z).toReal)) := by
  exact da_relative_result M Δs α hα0 hα1 hV q hq z hz hqz

#print axioms solution

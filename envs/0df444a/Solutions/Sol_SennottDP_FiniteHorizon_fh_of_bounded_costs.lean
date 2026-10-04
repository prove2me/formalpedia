-- Prove2me | solution 1 for SennottDP.FiniteHorizon.fh_of_bounded_costs
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-03T23:13:50.951453+00:00
-- url     : https://prove2.me/submissions/c7ce8b43-38d0-4b5d-b761-baf294d1a87a

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

open SennottDP.FiniteHorizon

/-- Proposition 3.3.1 (Sennott, p. 45). Let `(Δ_N)` be an approximating sequence for `Δ`. Assume
that there is a finite constant `B` with `C(i, a) ≤ B` and `F(i) ≤ B` for all state-action pairs.
Then FH(α, n) holds for all `α ∈ (0, 1]` and `n ≥ 1`. -/
theorem solution {S Act : Type} [Countable S] (M : MDC S Act) (F : S → ℝ≥0)
    (AS : M.ApproxSeq) (B : ℝ≥0) (hC : ∀ i, ∀ a ∈ M.A i, M.C i a ≤ B) (hF : ∀ i, F i ≤ B) :
    ∀ α : ℝ≥0, 0 < α → α ≤ 1 → ∀ n, 1 ≤ n → AS.FH F α n := by
  exact fa_bounded_result M F AS B hC hF

#print axioms solution

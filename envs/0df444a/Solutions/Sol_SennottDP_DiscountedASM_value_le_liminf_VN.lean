-- Prove2me | solution 1 for SennottDP.DiscountedASM.value_le_liminf_VN
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-03T23:32:17.117167+00:00
-- url     : https://prove2.me/submissions/e08e76f6-692f-4d27-bb43-51f152e77c55

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

open SennottDP.DiscountedASM

/-- Lemma 4.6.2 (p. 75): `liminf_{N→∞} V^N_α ≥ V_α`, pointwise on `S`. -/
theorem solution {S Act : Type} [Countable S] (M : MDC S Act)
    (Δs : ApproxSeq M) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1) (i : S) :
    M.value α i ≤ liminf (fun N => Δs.VN α N i) atTop := by
  exact da_liminf M Δs α i

#print axioms solution

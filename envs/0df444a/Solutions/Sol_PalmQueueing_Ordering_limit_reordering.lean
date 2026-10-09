-- Prove2me | solution 1 for PalmQueueing.Ordering.limit_reordering
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T15:36:54.718342+00:00
-- url     : https://prove2.me/submissions/b98c0c6f-a6fd-46fb-9fa9-aab8c907d751

import Mathlib
import Definitions.Def_PalmQueueing_Ordering_Disciplines


set_option autoImplicit false
open PalmQueueing.Ordering
namespace InterchangeRun
lemma oldest_waiting (cust : Set ℕ) (T : ℕ → ℝ) (s : SchedState)
    (hu : (unserved cust s).Nonempty) : sInf (unserved cust s) ∈ waiting cust T s := by
  exact ⟨Nat.sInf_mem hu,le_max_right _ _⟩
lemma pick_waiting (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ) (s : SchedState)
    (hu : (unserved cust s).Nonempty) : pick φ cust T σ U s ∈ waiting cust T s := by
  unfold pick
  split_ifs with h
  · exact h
  · exact oldest_waiting cust T s hu
lemma pick_unserved (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ) (s : SchedState)
    (hu : (unserved cust s).Nonempty) : pick φ cust T σ U s ∈ unserved cust s :=
  (pick_waiting φ cust T σ U s hu).1
lemma run_nodup (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ) (m : ℕ) :
    (run φ cust T σ U m).served.Nodup := by
  induction m with
  | zero => simp [run]
  | succ m ih =>
    rw [run]
    unfold step
    split_ifs with hu
    · change ((run φ cust T σ U m).served ++ [pick φ cust T σ U (run φ cust T σ U m)]).Nodup
      rw [← List.concat_eq_append,List.nodup_concat]
      exact ⟨(pick_unserved φ cust T σ U _ hu).2,ih⟩
    · exact ih
lemma run_mem_cust (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ) (m : ℕ) :
    ∀ k ∈ (run φ cust T σ U m).served, k ∈ cust := by
  induction m with
  | zero => simp [run]
  | succ m ih =>
    rw [run]
    unfold step
    split_ifs with hu
    · intro k hk
      simp only [List.mem_append,List.mem_singleton] at hk
      rcases hk with hk | hk
      · exact ih k hk
      · subst k
        exact (pick_unserved φ cust T σ U _ hu).1
    · exact ih
lemma run_length_le (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ) (m : ℕ) :
    (run φ cust T σ U m).served.length ≤ m := by
  induction m with
  | zero => simp [run]
  | succ m ih =>
    rw [run]
    unfold step
    split_ifs with hu
    · simp only [List.length_append,List.length_singleton]
      omega
    · exact ih.trans (Nat.le_succ _)
end InterchangeRun
#print axioms InterchangeRun.oldest_waiting
#print axioms InterchangeRun.pick_waiting
#print axioms InterchangeRun.pick_unserved
#print axioms InterchangeRun.run_nodup
#print axioms InterchangeRun.run_mem_cust
#print axioms InterchangeRun.run_length_le

set_option autoImplicit false
open PalmQueueing.Ordering InterchangeRun
namespace InterchangeFiniteRun
lemma unserved_nonempty_of_short (φ : Discipline) (T σ U : ℕ → ℝ) (n m : ℕ)
    (hl : (run φ {k | k ≤ n} T σ U m).served.length < n+1) :
    (unserved {k | k ≤ n} (run φ {k | k ≤ n} T σ U m)).Nonempty := by
  by_contra h
  have hs : Finset.range (n+1) ⊆ (run φ {k | k ≤ n} T σ U m).served.toFinset := by
    intro k hk
    apply List.mem_toFinset.mpr
    by_contra hn
    have hkn : k ≤ n := by have hh := Finset.mem_range.mp hk; omega
    exact h ⟨k,hkn,hn⟩
  have hh := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup (run_nodup φ _ T σ U m)] at hh
  simp only [Finset.card_range] at hh
  omega
lemma finite_run_length (φ : Discipline) (T σ U : ℕ → ℝ) (n m : ℕ) (hm : m ≤ n+1) :
    (run φ {k | k ≤ n} T σ U m).served.length = m := by
  induction m with
  | zero => simp [run]
  | succ m ih =>
    have hml : m ≤ n+1 := by omega
    have hlen := ih hml
    have hu := unserved_nonempty_of_short φ T σ U n m (by rw [hlen]; omega)
    rw [run,step,if_pos hu]
    simp only [List.length_append,List.length_singleton,hlen]
lemma finite_run_full_set (φ : Discipline) (T σ U : ℕ → ℝ) (n : ℕ) :
    (run φ {k | k ≤ n} T σ U (n+1)).served.toFinset = Finset.range (n+1) := by
  apply Finset.eq_of_subset_of_card_le
  · intro k hk
    have hh := run_mem_cust φ {k | k ≤ n} T σ U (n+1) k (List.mem_toFinset.mp hk)
    change k ≤ n at hh
    apply Finset.mem_range.mpr
    omega
  · rw [List.toFinset_card_of_nodup (run_nodup φ _ T σ U (n+1)),
      finite_run_length φ T σ U n (n+1) le_rfl,Finset.card_range]
lemma finite_run_succ (φ : Discipline) (T σ U : ℕ → ℝ) (n m : ℕ) (hm : m ≤ n) :
    (run φ {k | k ≤ n} T σ U (m+1)).served =
      (run φ {k | k ≤ n} T σ U m).served ++
        [pick φ {k | k ≤ n} T σ U (run φ {k | k ≤ n} T σ U m)] := by
  have hu := unserved_nonempty_of_short φ T σ U n m
    (by rw [finite_run_length φ T σ U n m (by omega)]; omega)
  rw [run,step,if_pos hu]
lemma finite_run_prefix (φ : Discipline) (T σ U : ℕ → ℝ) (n m r : ℕ)
    (hmr : m ≤ r) (hr : r ≤ n+1) :
    (run φ {k | k ≤ n} T σ U m).served.IsPrefix
      (run φ {k | k ≤ n} T σ U r).served := by
  obtain ⟨q,rfl⟩ := Nat.exists_eq_add_of_le hmr
  clear hmr
  induction q with
  | zero => simp
  | succ q ih =>
    have hmq : m+q ≤ n := by omega
    rw [show m+q.succ = (m+q)+1 by omega,finite_run_succ φ T σ U n (m+q) hmq]
    exact (ih (by omega)).trans (List.prefix_append _ _)
end InterchangeFiniteRun
#print axioms InterchangeFiniteRun.unserved_nonempty_of_short
#print axioms InterchangeFiniteRun.finite_run_length
#print axioms InterchangeFiniteRun.finite_run_full_set
#print axioms InterchangeFiniteRun.finite_run_succ
#print axioms InterchangeFiniteRun.finite_run_prefix

set_option autoImplicit false
open PalmQueueing.Ordering InterchangeRun InterchangeFiniteRun
namespace InterchangePermutation
lemma finite_run_pick_get (φ : Discipline) (T σ U : ℕ → ℝ) (n m : ℕ) (hm : m ≤ n) :
    (run φ {k | k ≤ n} T σ U (n+1)).served.get
      ⟨m,by rw [finite_run_length φ T σ U n (n+1) le_rfl]; omega⟩ =
        pick φ {k | k ≤ n} T σ U (run φ {k | k ≤ n} T σ U m) := by
  have hp := finite_run_prefix φ T σ U n (m+1) (n+1) (by omega) le_rfl
  have hlen := finite_run_length φ T σ U n m (by omega)
  have hlt : m < (run φ {k | k ≤ n} T σ U (m+1)).served.length := by
    rw [finite_run_length φ T σ U n (m+1) (by omega)]
    omega
  simpa [finite_run_succ φ T σ U n m hm,hlen] using (hp.getElem hlt).symm
lemma rankPerm_get (φ : Discipline) (T σ U : ℕ → ℝ) (n m : ℕ) (hm : m ≤ n) :
    rankPerm φ T σ U n m = (run φ {k | k ≤ n} T σ U (n+1)).served.get
      ⟨m,by rw [finite_run_length φ T σ U n (n+1) le_rfl]; omega⟩ := by
  rw [rankPerm,if_pos hm]
  exact (finite_run_pick_get φ T σ U n m hm).symm
lemma rankPerm_le (φ : Discipline) (T σ U : ℕ → ℝ) (n m : ℕ) (hm : m ≤ n) :
    rankPerm φ T σ U n m ≤ n := by
  rw [rankPerm_get φ T σ U n m hm]
  exact run_mem_cust φ {k | k ≤ n} T σ U (n+1) _ (List.get_mem _ _)
lemma rankPerm_fixed_beyond (φ : Discipline) (T σ U : ℕ → ℝ) (n : ℕ) :
    PermFixedBeyond (rankPerm φ T σ U n) n := by
  classical
  have hfixed : ∀ k : ℕ, n < k → rankPerm φ T σ U n k = k := by
    intro k hk
    simp only [rankPerm,not_le.mpr hk,↓reduceIte]
  have hinj : Function.Injective (rankPerm φ T σ U n) := by
    intro i j hij
    by_cases hi : i ≤ n
    · by_cases hj : j ≤ n
      · rw [rankPerm_get φ T σ U n i hi,rankPerm_get φ T σ U n j hj] at hij
        have he := (run_nodup φ {k | k ≤ n} T σ U (n+1)).get_inj_iff.mp hij
        exact congrArg Fin.val he
      · rw [hfixed j (lt_of_not_ge hj)] at hij
        have hh := rankPerm_le φ T σ U n i hi
        omega
    · by_cases hj : j ≤ n
      · rw [hfixed i (lt_of_not_ge hi)] at hij
        have hh := rankPerm_le φ T σ U n j hj
        omega
      · rwa [hfixed i (lt_of_not_ge hi),hfixed j (lt_of_not_ge hj)] at hij
  have hsurj : Function.Surjective (rankPerm φ T σ U n) := by
    intro k
    by_cases hk : k ≤ n
    · have hmem : k ∈ (run φ {i | i ≤ n} T σ U (n+1)).served := by
        apply List.mem_toFinset.mp
        rw [finite_run_full_set φ T σ U n]
        exact Finset.mem_range.mpr (by omega)
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp hmem
      have hin : (i : ℕ) ≤ n := by
        have hh := i.isLt
        have hlen := finite_run_length φ T σ U n (n+1) le_rfl
        omega
      refine ⟨i,?_⟩
      rw [rankPerm_get φ T σ U n i hin]
      exact hi
    · exact ⟨k,hfixed k (lt_of_not_ge hk)⟩
  exact ⟨⟨hinj,hsurj⟩,hfixed⟩
end InterchangePermutation
#print axioms InterchangePermutation.finite_run_pick_get
#print axioms InterchangePermutation.rankPerm_get
#print axioms InterchangePermutation.rankPerm_le
#print axioms InterchangePermutation.rankPerm_fixed_beyond

set_option autoImplicit false
open MeasureTheory PalmQueueing.Ordering InterchangePermutation
namespace InterchangeCandidate
noncomputable def candidate {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (A : GIGIInput Ω P) (φ : Discipline) : ℕ → Ω → ℕ → ℕ :=
  fun n ω => rankPerm φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) n
lemma candidate_first_original_obligation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : GIGIInput Ω P) (φ : Discipline) :
    ∀ (n : ℕ) (ω : Ω), PermFixedBeyond (candidate A φ n ω) n := by
  intro n ω
  exact rankPerm_fixed_beyond φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) n
end InterchangeCandidate
#print axioms InterchangeCandidate.candidate_first_original_obligation

set_option autoImplicit false
open PalmQueueing.Ordering InterchangeRun
namespace InterchangePrefixStep
lemma oldest_prefix_eq (n : ℕ) (s : SchedState)
    (hu : (unserved {k | k ≤ n} s).Nonempty) :
    sInf (unserved Set.univ s) = sInf (unserved {k | k ≤ n} s) := by
  have hf := Nat.sInf_mem hu
  have hgU : (unserved Set.univ s).Nonempty := ⟨_,Set.mem_univ _,hf.2⟩
  have hg := Nat.sInf_mem hgU
  have hle : sInf (unserved Set.univ s) ≤ sInf (unserved {k | k ≤ n} s) :=
    Nat.sInf_le ⟨Set.mem_univ _,hf.2⟩
  apply le_antisymm hle
  apply Nat.sInf_le
  exact ⟨hle.trans hf.1,hg.2⟩
lemma epoch_prefix_eq (T : ℕ → ℝ) (n : ℕ) (s : SchedState)
    (hu : (unserved {k | k ≤ n} s).Nonempty) :
    epoch Set.univ T s = epoch {k | k ≤ n} T s := by
  unfold epoch
  rw [oldest_prefix_eq n s hu]
lemma waiting_prefix_eq (T : ℕ → ℝ) (hT : StrictMono T) (n : ℕ) (s : SchedState)
    (hu : (unserved {k | k ≤ n} s).Nonempty) (ht : epoch {k | k ≤ n} T s ≤ T n) :
    waiting Set.univ T s = waiting {k | k ≤ n} T s := by
  ext k
  unfold waiting
  rw [epoch_prefix_eq T n s hu]
  constructor
  · intro hk
    exact ⟨⟨hT.le_iff_le.mp (hk.2.trans ht),hk.1.2⟩,hk.2⟩
  · intro hk
    exact ⟨⟨Set.mem_univ _,hk.1.2⟩,hk.2⟩
lemma pick_prefix_eq (φ : Discipline) (T σ U : ℕ → ℝ) (hT : StrictMono T)
    (n : ℕ) (s : SchedState) (hu : (unserved {k | k ≤ n} s).Nonempty)
    (ht : epoch {k | k ≤ n} T s ≤ T n) :
    pick φ Set.univ T σ U s = pick φ {k | k ≤ n} T σ U s := by
  unfold pick
  simp only [epoch_prefix_eq T n s hu,waiting_prefix_eq T hT n s hu ht,oldest_prefix_eq n s hu]
  all_goals split_ifs <;> simp_all [epoch_prefix_eq T n s hu,waiting_prefix_eq T hT n s hu ht]
lemma step_prefix_eq (φ : Discipline) (T σ U : ℕ → ℝ) (hT : StrictMono T)
    (n : ℕ) (s : SchedState) (hu : (unserved {k | k ≤ n} s).Nonempty)
    (ht : epoch {k | k ≤ n} T s ≤ T n) :
    step φ Set.univ T σ U s = step φ {k | k ≤ n} T σ U s := by
  have hg : (unserved Set.univ s).Nonempty := by
    obtain ⟨k,hk⟩ := hu
    exact ⟨k,Set.mem_univ _,hk.2⟩
  unfold step
  simp only [hg,hu,↓reduceIte,pick_prefix_eq φ T σ U hT n s hu ht,epoch_prefix_eq T n s hu]
end InterchangePrefixStep
#print axioms InterchangePrefixStep.oldest_prefix_eq
#print axioms InterchangePrefixStep.epoch_prefix_eq
#print axioms InterchangePrefixStep.waiting_prefix_eq
#print axioms InterchangePrefixStep.pick_prefix_eq
#print axioms InterchangePrefixStep.step_prefix_eq

set_option autoImplicit false
open PalmQueueing.Ordering InterchangeRun
namespace InterchangeTime
lemma step_free_ge (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ) (s : SchedState)
    (hσ : ∀ k, 0 ≤ σ k) : s.free ≤ (step φ cust T σ U s).free := by
  unfold step
  split_ifs
  · exact (le_max_left _ _).trans (le_add_of_nonneg_right (hσ _))
  · rfl
lemma run_free_monotone (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ)
    (hσ : ∀ k, 0 ≤ σ k) : Monotone (fun m => (run φ cust T σ U m).free) := by
  apply monotone_nat_of_le_succ
  intro m
  exact step_free_ge φ cust T σ U _ hσ
lemma served_arrival_le_free (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ)
    (hσ : ∀ k, 0 ≤ σ k) (m : ℕ) :
    ∀ k ∈ (run φ cust T σ U m).served, T k ≤ (run φ cust T σ U m).free := by
  induction m with
  | zero => simp [run]
  | succ m ih =>
    rw [run]
    unfold step
    split_ifs with hu
    · intro k hk
      simp only [List.mem_append,List.mem_singleton] at hk
      rcases hk with hk | hk
      · exact (ih k hk).trans ((le_max_left _ _).trans (le_add_of_nonneg_right (hσ _)))
      · subst k
        exact (pick_waiting φ cust T σ U _ hu).2.trans (le_add_of_nonneg_right (hσ _))
    · exact ih
end InterchangeTime
#print axioms InterchangeTime.step_free_ge
#print axioms InterchangeTime.run_free_monotone
#print axioms InterchangeTime.served_arrival_le_free

set_option autoImplicit false
open PalmQueueing.Ordering InterchangeRun InterchangeFiniteRun InterchangeTime
namespace InterchangeEpoch
lemma missing_le_length (l : List ℕ) : ∃ k : ℕ, k ≤ l.length ∧ k ∉ l := by
  by_contra h
  have hs : Finset.range (l.length+1) ⊆ l.toFinset := by
    intro k hk
    apply List.mem_toFinset.mpr
    by_contra hn
    exact h ⟨k,by have hh := Finset.mem_range.mp hk; omega,hn⟩
  have hh := (Finset.card_le_card hs).trans l.toFinset_card_le
  simp only [Finset.card_range] at hh
  omega
lemma large_served_of_hole (l : List ℕ) (hl : l.Nodup) (m j : ℕ)
    (hlen : l.length = m) (hj : j < m) (hnot : j ∉ l) : ∃ k ∈ l, m ≤ k := by
  by_contra h
  have hs : l.toFinset ⊆ Finset.range m := by
    intro k hk
    apply Finset.mem_range.mpr
    by_contra hn
    exact h ⟨k,List.mem_toFinset.mp hk,le_of_not_gt hn⟩
  have he : l.toFinset = Finset.range m := Finset.eq_of_subset_of_card_le hs
    (by rw [List.toFinset_card_of_nodup hl,hlen,Finset.card_range])
  apply hnot
  apply List.mem_toFinset.mp
  rw [he]
  exact Finset.mem_range.mpr hj
lemma oldest_le_rank (φ : Discipline) (T σ U : ℕ → ℝ) (n m : ℕ) (hm : m ≤ n) :
    sInf (unserved {k | k ≤ n} (run φ {k | k ≤ n} T σ U m)) ≤ m := by
  obtain ⟨k,hk,hn⟩ := missing_le_length (run φ {k | k ≤ n} T σ U m).served
  rw [finite_run_length φ T σ U n m (by omega)] at hk
  have hku : k ∈ unserved {j | j ≤ n} (run φ {j | j ≤ n} T σ U m) := ⟨hk.trans hm,hn⟩
  exact (Nat.sInf_le hku).trans hk
lemma finite_epoch_by_rank (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (n m : ℕ) (hm : m ≤ n) :
    epoch {k | k ≤ n} T (run φ {k | k ≤ n} T σ U m) =
      max (run φ {k | k ≤ n} T σ U m).free (T m) := by
  let s := run φ {k | k ≤ n} T σ U m
  let j := sInf (unserved {k | k ≤ n} s)
  have hlen : s.served.length = m := finite_run_length φ T σ U n m (by omega)
  have hu : (unserved {k | k ≤ n} s).Nonempty :=
    unserved_nonempty_of_short φ T σ U n m (by rw [hlen]; omega)
  have hj : j ≤ m := oldest_le_rank φ T σ U n m hm
  change max s.free (T j) = max s.free (T m)
  rcases hj.eq_or_lt with hj | hj
  · rw [hj]
  · have hnot : j ∉ s.served := (Nat.sInf_mem hu).2
    obtain ⟨k,hk,hmk⟩ := large_served_of_hole s.served (run_nodup φ _ T σ U m) m j hlen hj hnot
    have hf : T m ≤ s.free := (hT.monotone hmk).trans
      (served_arrival_le_free φ _ T σ U hσ m k hk)
    rw [max_eq_left ((hT.monotone hj.le).trans hf),max_eq_left hf]
end InterchangeEpoch
#print axioms InterchangeEpoch.missing_le_length
#print axioms InterchangeEpoch.large_served_of_hole
#print axioms InterchangeEpoch.oldest_le_rank
#print axioms InterchangeEpoch.finite_epoch_by_rank

set_option autoImplicit false
open PalmQueueing.Ordering InterchangeRun InterchangeTime InterchangeEpoch InterchangeFiniteRun InterchangePrefixStep
namespace InterchangeFullProjection
lemma full_unserved_nonempty (s : SchedState) : (unserved Set.univ s).Nonempty := by
  obtain ⟨k,_,hk⟩ := missing_le_length s.served
  exact ⟨k,Set.mem_univ _,hk⟩
lemma full_run_length (φ : Discipline) (T σ U : ℕ → ℝ) (m : ℕ) :
    (run φ Set.univ T σ U m).served.length = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [run,step,if_pos (full_unserved_nonempty _)]
    simp only [List.length_append,List.length_singleton,ih]
lemma full_oldest_le_rank (φ : Discipline) (T σ U : ℕ → ℝ) (m : ℕ) :
    sInf (unserved Set.univ (run φ Set.univ T σ U m)) ≤ m := by
  obtain ⟨k,hk,hn⟩ := missing_le_length (run φ Set.univ T σ U m).served
  rw [full_run_length] at hk
  exact (Nat.sInf_le (show k ∈ unserved Set.univ (run φ Set.univ T σ U m) from ⟨Set.mem_univ _,hn⟩)).trans hk
lemma full_epoch_by_rank (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (m : ℕ) :
    epoch Set.univ T (run φ Set.univ T σ U m) = max (run φ Set.univ T σ U m).free (T m) := by
  let s := run φ Set.univ T σ U m
  let j := sInf (unserved Set.univ s)
  have hj : j ≤ m := full_oldest_le_rank φ T σ U m
  change max s.free (T j) = max s.free (T m)
  rcases hj.eq_or_lt with hj | hj
  · rw [hj]
  · have hnot : j ∉ s.served := (Nat.sInf_mem (full_unserved_nonempty s)).2
    obtain ⟨k,hk,hmk⟩ := large_served_of_hole s.served (run_nodup φ _ T σ U m) m j
      (full_run_length φ T σ U m) hj hnot
    have hf : T m ≤ s.free := (hT.monotone hmk).trans (served_arrival_le_free φ _ T σ U hσ m k hk)
    rw [max_eq_left ((hT.monotone hj.le).trans hf),max_eq_left hf]
lemma full_epoch_monotone (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) :
    Monotone (fun m => epoch Set.univ T (run φ Set.univ T σ U m)) := by
  intro m r hmr
  dsimp only
  rw [full_epoch_by_rank φ T σ U hT hσ m,full_epoch_by_rank φ T σ U hT hσ r]
  exact max_le_max (run_free_monotone φ _ T σ U hσ hmr) (hT.monotone hmr)
lemma full_rank_le_of_epoch_le (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (n m : ℕ)
    (ht : epoch Set.univ T (run φ Set.univ T σ U m) ≤ T n) : m ≤ n := by
  apply hT.le_iff_le.mp
  rw [full_epoch_by_rank φ T σ U hT hσ m] at ht
  exact (le_max_right _ _).trans ht
lemma full_run_eq_prefix_of_epoch_le (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (n m : ℕ)
    (ht : epoch Set.univ T (run φ Set.univ T σ U m) ≤ T n) :
    run φ Set.univ T σ U m = run φ {k | k ≤ n} T σ U m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hp : epoch Set.univ T (run φ Set.univ T σ U m) ≤ T n :=
      (full_epoch_monotone φ T σ U hT hσ (by omega)).trans ht
    have hs := ih hp
    have hm : m ≤ n := full_rank_le_of_epoch_le φ T σ U hT hσ n m hp
    have hu := unserved_nonempty_of_short φ T σ U n m
      (by rw [finite_run_length φ T σ U n m (by omega)]; omega)
    have hep : epoch {k | k ≤ n} T (run φ {k | k ≤ n} T σ U m) ≤ T n := by
      rw [hs,epoch_prefix_eq T n _ hu] at hp
      exact hp
    rw [run,run,hs]
    exact step_prefix_eq φ T σ U hT n _ hu hep
end InterchangeFullProjection
#print axioms InterchangeFullProjection.full_unserved_nonempty
#print axioms InterchangeFullProjection.full_run_length
#print axioms InterchangeFullProjection.full_oldest_le_rank
#print axioms InterchangeFullProjection.full_epoch_by_rank
#print axioms InterchangeFullProjection.full_epoch_monotone
#print axioms InterchangeFullProjection.full_rank_le_of_epoch_le
#print axioms InterchangeFullProjection.full_run_eq_prefix_of_epoch_le

set_option autoImplicit false
open PalmQueueing.Ordering InterchangeRun
namespace InterchangeServiceRank
lemma run_succ_prefix (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ) (m : ℕ) :
    (run φ cust T σ U m).served.IsPrefix (run φ cust T σ U (m+1)).served := by
  rw [run]
  unfold step
  split_ifs
  · exact List.prefix_append _ _
  · simp
lemma run_prefix (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ) (m r : ℕ) (hm : m ≤ r) :
    (run φ cust T σ U m).served.IsPrefix (run φ cust T σ U r).served := by
  obtain ⟨q,rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hm
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show m+q.succ = (m+q)+1 by omega]
    exact ih.trans (run_succ_prefix φ cust T σ U (m+q))
lemma servedAt_mem_after (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ) (k m : ℕ)
    (hm : ServedAt φ cust T σ U k m) : k ∈ (run φ cust T σ U (m+1)).served := by
  rw [run,step,if_pos hm.1]
  simp only [List.mem_append,List.mem_singleton,hm.2,or_true]
lemma servedAt_not_mem_before (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ) (k m : ℕ)
    (hm : ServedAt φ cust T σ U k m) : k ∉ (run φ cust T σ U m).served := by
  have hh := (pick_unserved φ cust T σ U _ hm.1).2
  rwa [hm.2] at hh
lemma servedAt_unique (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ) (k m r : ℕ)
    (hm : ServedAt φ cust T σ U k m) (hr : ServedAt φ cust T σ U k r) : m = r := by
  have hnot : ¬m < r := by
    intro h
    have hp := run_prefix φ cust T σ U (m+1) r (by omega)
    exact servedAt_not_mem_before φ cust T σ U k r hr
      (hp.subset (servedAt_mem_after φ cust T σ U k m hm))
  have hnot' : ¬r < m := by
    intro h
    have hp := run_prefix φ cust T σ U (r+1) m (by omega)
    exact servedAt_not_mem_before φ cust T σ U k m hm
      (hp.subset (servedAt_mem_after φ cust T σ U k r hr))
  omega
lemma beginTime_eq_epoch_of_servedAt (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ)
    (k m : ℕ) (hm : ServedAt φ cust T σ U k m) :
    beginTime φ cust T σ U k = epoch cust T (run φ cust T σ U m) := by
  classical
  have he : ∃ r, ServedAt φ cust T σ U k r := ⟨m,hm⟩
  rw [beginTime,dif_pos he]
  have hf : Nat.find he = m := servedAt_unique φ cust T σ U k _ m (Nat.find_spec he) hm
  rw [hf]
lemma departTime_eq_epoch_service_of_servedAt (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ)
    (k m : ℕ) (hm : ServedAt φ cust T σ U k m) :
    departTime φ cust T σ U k = epoch cust T (run φ cust T σ U m)+σ k := by
  rw [departTime,beginTime_eq_epoch_of_servedAt φ cust T σ U k m hm]
lemma started_by_iff (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ) (k : ℕ) (t : ℝ) :
    (IsServed φ cust T σ U k ∧ beginTime φ cust T σ U k ≤ t) ↔
      ∃ m, ServedAt φ cust T σ U k m ∧ epoch cust T (run φ cust T σ U m) ≤ t := by
  constructor
  · rintro ⟨⟨m,hm⟩,ht⟩
    exact ⟨m,hm,(beginTime_eq_epoch_of_servedAt φ cust T σ U k m hm) ▸ ht⟩
  · rintro ⟨m,hm,ht⟩
    exact ⟨⟨m,hm⟩,by rwa [beginTime_eq_epoch_of_servedAt φ cust T σ U k m hm]⟩
lemma departed_by_iff (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ) (k : ℕ) (t : ℝ) :
    (IsServed φ cust T σ U k ∧ departTime φ cust T σ U k ≤ t) ↔
      ∃ m, ServedAt φ cust T σ U k m ∧ epoch cust T (run φ cust T σ U m)+σ k ≤ t := by
  constructor
  · rintro ⟨⟨m,hm⟩,ht⟩
    exact ⟨m,hm,(departTime_eq_epoch_service_of_servedAt φ cust T σ U k m hm) ▸ ht⟩
  · rintro ⟨m,hm,ht⟩
    exact ⟨⟨m,hm⟩,by rwa [departTime_eq_epoch_service_of_servedAt φ cust T σ U k m hm]⟩
end InterchangeServiceRank
#print axioms InterchangeServiceRank.run_succ_prefix
#print axioms InterchangeServiceRank.run_prefix
#print axioms InterchangeServiceRank.servedAt_mem_after
#print axioms InterchangeServiceRank.servedAt_not_mem_before
#print axioms InterchangeServiceRank.servedAt_unique
#print axioms InterchangeServiceRank.beginTime_eq_epoch_of_servedAt
#print axioms InterchangeServiceRank.departTime_eq_epoch_service_of_servedAt

#print axioms InterchangeServiceRank.started_by_iff
#print axioms InterchangeServiceRank.departed_by_iff

set_option autoImplicit false
open PalmQueueing.Ordering InterchangeRun InterchangeTime InterchangeEpoch InterchangeFiniteRun InterchangePrefixStep InterchangeFullProjection InterchangeServiceRank
namespace InterchangeEvents
lemma run_eq_of_finite_epoch_le (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (n m : ℕ) (hm : m ≤ n)
    (ht : epoch {k | k ≤ n} T (run φ {k | k ≤ n} T σ U m) ≤ T n) :
    run φ Set.univ T σ U m = run φ {k | k ≤ n} T σ U m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hmn : m ≤ n := by omega
    have hp : epoch {k | k ≤ n} T (run φ {k | k ≤ n} T σ U m) ≤ T n := by
      apply le_trans _ ht
      rw [finite_epoch_by_rank φ T σ U hT hσ n m hmn,
        finite_epoch_by_rank φ T σ U hT hσ n (m+1) hm]
      exact max_le_max (run_free_monotone φ _ T σ U hσ (by omega)) (hT.monotone (by omega))
    have hs := ih hmn hp
    have hu := unserved_nonempty_of_short φ T σ U n m
      (by rw [finite_run_length φ T σ U n m (by omega)]; omega)
    rw [run,run,hs]
    exact step_prefix_eq φ T σ U hT n _ hu hp
lemma finite_servedAt_rank_le (φ : Discipline) (T σ U : ℕ → ℝ) (n k m : ℕ)
    (hm : ServedAt φ {j | j ≤ n} T σ U k m) : m ≤ n := by
  by_contra h
  obtain ⟨j,hj⟩ := hm.1
  have hmem : j ∈ (run φ {k | k ≤ n} T σ U (n+1)).served := by
    apply List.mem_toFinset.mp
    rw [finite_run_full_set]
    exact Finset.mem_range.mpr (by have hh : j ≤ n := hj.1; omega)
  have hp := run_prefix φ {k | k ≤ n} T σ U (n+1) m (by omega)
  exact hj.2 (hp.subset hmem)
lemma rank_event_prefix_iff (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (n k m : ℕ) (t : ℝ) (htn : t ≤ T n) :
    (ServedAt φ Set.univ T σ U k m ∧ epoch Set.univ T (run φ Set.univ T σ U m) ≤ t) ↔
    (ServedAt φ {j | j ≤ n} T σ U k m ∧ epoch {j | j ≤ n} T (run φ {j | j ≤ n} T σ U m) ≤ t) := by
  constructor
  · rintro ⟨hk,ht⟩
    have hm := full_rank_le_of_epoch_le φ T σ U hT hσ n m (ht.trans htn)
    have hs := full_run_eq_prefix_of_epoch_le φ T σ U hT hσ n m (ht.trans htn)
    have hu := unserved_nonempty_of_short φ T σ U n m
      (by rw [finite_run_length φ T σ U n m (by omega)]; omega)
    have he : epoch Set.univ T (run φ Set.univ T σ U m) = epoch {j | j ≤ n} T (run φ {j | j ≤ n} T σ U m) := by
      rw [hs,epoch_prefix_eq T n _ hu]
    have hep : epoch {j | j ≤ n} T (run φ {j | j ≤ n} T σ U m) ≤ t := he ▸ ht
    refine ⟨⟨hu,?_⟩,hep⟩
    have hp := hk.2
    rw [hs,pick_prefix_eq φ T σ U hT n _ hu (hep.trans htn)] at hp
    exact hp
  · rintro ⟨hk,ht⟩
    have hm := finite_servedAt_rank_le φ T σ U n k m hk
    have hs := run_eq_of_finite_epoch_le φ T σ U hT hσ n m hm (ht.trans htn)
    refine ⟨⟨full_unserved_nonempty _,?_⟩,?_⟩
    · rw [hs,pick_prefix_eq φ T σ U hT n _ hk.1 (ht.trans htn)]
      exact hk.2
    · rw [hs,epoch_prefix_eq T n _ hk.1]
      exact ht
lemma started_prefix_iff (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (n k : ℕ) (t : ℝ) (htn : t ≤ T n) :
    (IsServed φ Set.univ T σ U k ∧ beginTime φ Set.univ T σ U k ≤ t) ↔
    (IsServed φ {j | j ≤ n} T σ U k ∧ beginTime φ {j | j ≤ n} T σ U k ≤ t) := by
  rw [started_by_iff,started_by_iff]
  exact exists_congr (fun m => rank_event_prefix_iff φ T σ U hT hσ n k m t htn)
lemma departed_prefix_iff (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (n k : ℕ) (t : ℝ) (htn : t ≤ T n) :
    (IsServed φ Set.univ T σ U k ∧ departTime φ Set.univ T σ U k ≤ t) ↔
    (IsServed φ {j | j ≤ n} T σ U k ∧ departTime φ {j | j ≤ n} T σ U k ≤ t) := by
  rw [departed_by_iff,departed_by_iff]
  constructor
  · rintro ⟨m,hk,hd⟩
    have ht : epoch Set.univ T (run φ Set.univ T σ U m) ≤ t :=
      (le_add_of_nonneg_right (hσ k)).trans hd
    have hf := (rank_event_prefix_iff φ T σ U hT hσ n k m t htn).mp ⟨hk,ht⟩
    have hs := full_run_eq_prefix_of_epoch_le φ T σ U hT hσ n m (ht.trans htn)
    refine ⟨m,hf.1,?_⟩
    rw [hs,epoch_prefix_eq T n _ hf.1.1] at hd
    exact hd
  · rintro ⟨m,hk,hd⟩
    have ht : epoch {j | j ≤ n} T (run φ {j | j ≤ n} T σ U m) ≤ t :=
      (le_add_of_nonneg_right (hσ k)).trans hd
    have hf := (rank_event_prefix_iff φ T σ U hT hσ n k m t htn).mpr ⟨hk,ht⟩
    have hm := finite_servedAt_rank_le φ T σ U n k m hk
    have hs := run_eq_of_finite_epoch_le φ T σ U hT hσ n m hm (ht.trans htn)
    refine ⟨m,hf.1,?_⟩
    rw [hs,epoch_prefix_eq T n _ hk.1]
    exact hd
end InterchangeEvents
#print axioms InterchangeEvents.run_eq_of_finite_epoch_le
#print axioms InterchangeEvents.finite_servedAt_rank_le
#print axioms InterchangeEvents.rank_event_prefix_iff
#print axioms InterchangeEvents.started_prefix_iff
#print axioms InterchangeEvents.departed_prefix_iff

set_option autoImplicit false
open PalmQueueing.Ordering InterchangeFiniteRun
namespace InterchangeFifo
lemma oldest_not_range (m : ℕ) : sInf {k : ℕ | k ∉ List.range m} = m := by
  have hm : m ∈ {k : ℕ | k ∉ List.range m} := by simp
  apply le_antisymm (Nat.sInf_le hm)
  have hs : sInf {k : ℕ | k ∉ List.range m} ∉ List.range m := Nat.sInf_mem (Set.nonempty_of_mem hm)
  exact le_of_not_gt (fun h => hs (List.mem_range.mpr h))
lemma fifo_pick_of_range (T σ U : ℕ → ℝ) (n m : ℕ) (hm : m ≤ n) (s : SchedState)
    (hl : s.served = List.range m) : pick fifo {k | k ≤ n} T σ U s = m := by
  have hmu : m ∈ unserved {k | k ≤ n} s := ⟨hm,by rw [hl]; simp⟩
  have hs : sInf (unserved {k | k ≤ n} s) = m := by
    apply le_antisymm (Nat.sInf_le hmu)
    have hh := (Nat.sInf_mem (Set.nonempty_of_mem hmu)).2
    rw [hl] at hh
    simpa only [List.mem_range,not_lt] using hh
  have hw : m ∈ waiting {k | k ≤ n} T s := by
    refine ⟨hmu,?_⟩
    rw [epoch,hs]
    exact le_max_right _ _
  have hsel : fifo.sel s.served (epoch {k | k ≤ n} T s) T
      (fun k => if k ∈ s.served then σ k else 0) U = m := by
    change sInf {k : ℕ | k ∉ s.served} = m
    rw [hl]
    exact oldest_not_range m
  unfold pick
  simp only [hsel,hw,↓reduceIte]
lemma fifo_run_served_range (T σ U : ℕ → ℝ) (n m : ℕ) (hm : m ≤ n+1) :
    (run fifo {k | k ≤ n} T σ U m).served = List.range m := by
  induction m with
  | zero => simp [run]
  | succ m ih =>
    have hmn : m ≤ n := by omega
    have hl := ih (by omega)
    rw [finite_run_succ fifo T σ U n m hmn,
      fifo_pick_of_range T σ U n m hmn _ hl,hl,List.range_succ]
end InterchangeFifo
#print axioms InterchangeFifo.oldest_not_range
#print axioms InterchangeFifo.fifo_pick_of_range
#print axioms InterchangeFifo.fifo_run_served_range

set_option autoImplicit false
open PalmQueueing.Ordering InterchangeFiniteRun InterchangePermutation InterchangeEpoch InterchangeFifo
namespace InterchangeClock
noncomputable def reorderedServices (φ : Discipline) (T σ U : ℕ → ℝ) (n : ℕ) : ℕ → ℝ :=
  fun k => σ (rankPerm φ T σ U n k)
lemma finite_free_clock_reordering (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (n m : ℕ) (hm : m ≤ n+1) :
    (run φ {k | k ≤ n} T σ U m).free =
      (run fifo {k | k ≤ n} T (reorderedServices φ T σ U n) U m).free := by
  let τ := reorderedServices φ T σ U n
  have hτ : ∀ k, 0 ≤ τ k := fun k => hσ _
  induction m with
  | zero => rfl
  | succ m ih =>
    have hmn : m ≤ n := by omega
    have hφU := unserved_nonempty_of_short φ T σ U n m
      (by rw [finite_run_length φ T σ U n m (by omega)]; omega)
    have hψU := unserved_nonempty_of_short fifo T τ U n m
      (by rw [finite_run_length fifo T τ U n m (by omega)]; omega)
    have hφstep : (run φ {k | k ≤ n} T σ U (m+1)).free =
        epoch {k | k ≤ n} T (run φ {k | k ≤ n} T σ U m) +
          σ (pick φ {k | k ≤ n} T σ U (run φ {k | k ≤ n} T σ U m)) := by
      rw [run,step,if_pos hφU]
    have hψstep : (run fifo {k | k ≤ n} T τ U (m+1)).free =
        epoch {k | k ≤ n} T (run fifo {k | k ≤ n} T τ U m) +
          τ (pick fifo {k | k ≤ n} T τ U (run fifo {k | k ≤ n} T τ U m)) := by
      rw [run,step,if_pos hψU]
    have hp : pick φ {k | k ≤ n} T σ U (run φ {k | k ≤ n} T σ U m) = rankPerm φ T σ U n m := by
      simp only [rankPerm,hmn,↓reduceIte]
    have hfp := fifo_pick_of_range T τ U n m hmn _ (fifo_run_served_range T τ U n m (by omega))
    change (run φ {k | k ≤ n} T σ U (m+1)).free = (run fifo {k | k ≤ n} T τ U (m+1)).free
    rw [hφstep,hψstep,finite_epoch_by_rank φ T σ U hT hσ n m hmn,
      finite_epoch_by_rank fifo T τ U hT hτ n m hmn,hfp,hp,ih (by omega)]
    rfl
lemma finite_epoch_reordering (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (n m : ℕ) (hm : m ≤ n) :
    epoch {k | k ≤ n} T (run φ {k | k ≤ n} T σ U m) =
      epoch {k | k ≤ n} T (run fifo {k | k ≤ n} T (reorderedServices φ T σ U n) U m) := by
  rw [finite_epoch_by_rank φ T σ U hT hσ n m hm,
    finite_epoch_by_rank fifo T (reorderedServices φ T σ U n) U hT (fun k => hσ _) n m hm,
    finite_free_clock_reordering φ T σ U hT hσ n m (by omega)]
end InterchangeClock
#print axioms InterchangeClock.finite_free_clock_reordering
#print axioms InterchangeClock.finite_epoch_reordering

set_option autoImplicit false
open PalmQueueing.Ordering InterchangeServiceRank InterchangeFiniteRun InterchangePermutation InterchangeFifo InterchangeClock
namespace InterchangeFiniteTimes
lemma finite_rank_servedAt (φ : Discipline) (T σ U : ℕ → ℝ) (n m : ℕ) (hm : m ≤ n) :
    ServedAt φ {k | k ≤ n} T σ U (rankPerm φ T σ U n m) m := by
  refine ⟨unserved_nonempty_of_short φ T σ U n m (by
    rw [finite_run_length φ T σ U n m (by omega)]; omega), ?_⟩
  simp only [rankPerm,hm,↓reduceIte]
lemma fifo_rank_servedAt (T σ U : ℕ → ℝ) (n m : ℕ) (hm : m ≤ n) :
    ServedAt fifo {k | k ≤ n} T σ U m m := by
  refine ⟨unserved_nonempty_of_short fifo T σ U n m (by
    rw [finite_run_length fifo T σ U n m (by omega)]; omega), ?_⟩
  exact fifo_pick_of_range T σ U n m hm _ (fifo_run_served_range T σ U n m (by omega))
lemma finite_rank_preimage (φ : Discipline) (T σ U : ℕ → ℝ) (n k : ℕ) (hk : k ≤ n) :
    ∃ m, m ≤ n ∧ rankPerm φ T σ U n m = k := by
  obtain ⟨m,hm⟩ := (rankPerm_fixed_beyond φ T σ U n).1.2 k
  refine ⟨m,?_,hm⟩
  by_contra h
  have hh := (rankPerm_fixed_beyond φ T σ U n).2 m (lt_of_not_ge h)
  omega
lemma finite_customer_isServed (φ : Discipline) (T σ U : ℕ → ℝ) (n k : ℕ) (hk : k ≤ n) :
    IsServed φ {j | j ≤ n} T σ U k := by
  obtain ⟨m,hm,hk'⟩ := finite_rank_preimage φ T σ U n k hk
  exact ⟨m,hk' ▸ finite_rank_servedAt φ T σ U n m hm⟩
lemma finite_begin_reordering (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (n m : ℕ) (hm : m ≤ n) :
    beginTime φ {k | k ≤ n} T σ U (rankPerm φ T σ U n m) =
      beginTime fifo {k | k ≤ n} T (reorderedServices φ T σ U n) U m := by
  rw [beginTime_eq_epoch_of_servedAt φ _ T σ U _ m (finite_rank_servedAt φ T σ U n m hm),
    beginTime_eq_epoch_of_servedAt fifo _ T _ U m m (fifo_rank_servedAt T _ U n m hm)]
  exact finite_epoch_reordering φ T σ U hT hσ n m hm
lemma finite_depart_reordering (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (n m : ℕ) (hm : m ≤ n) :
    departTime φ {k | k ≤ n} T σ U (rankPerm φ T σ U n m) =
      departTime fifo {k | k ≤ n} T (reorderedServices φ T σ U n) U m := by
  simp only [departTime,finite_begin_reordering φ T σ U hT hσ n m hm,reorderedServices]
end InterchangeFiniteTimes
#print axioms InterchangeFiniteTimes.finite_rank_servedAt
#print axioms InterchangeFiniteTimes.fifo_rank_servedAt
#print axioms InterchangeFiniteTimes.finite_rank_preimage
#print axioms InterchangeFiniteTimes.finite_customer_isServed
#print axioms InterchangeFiniteTimes.finite_begin_reordering
#print axioms InterchangeFiniteTimes.finite_depart_reordering

set_option autoImplicit false
open PalmQueueing.Ordering InterchangeRun InterchangeServiceRank InterchangePermutation InterchangeFiniteTimes InterchangeClock
namespace InterchangeFiniteCongestion
lemma arrival_le_depart_of_served (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → ℝ)
    (hσ : ∀ k, 0 ≤ σ k) (k : ℕ) (hk : IsServed φ cust T σ U k) :
    T k ≤ departTime φ cust T σ U k := by
  obtain ⟨m,hm⟩ := hk
  have hw := (pick_waiting φ cust T σ U _ hm.1).2
  rw [hm.2] at hw
  rw [departTime_eq_epoch_service_of_servedAt φ cust T σ U k m hm]
  exact hw.trans (le_add_of_nonneg_right (hσ k))
lemma finite_congestion_subtraction (φ : Discipline) (T σ U : ℕ → ℝ)
    (hσ : ∀ k, 0 ≤ σ k) (n : ℕ) (t : ℝ) :
    congestion φ {k | k ≤ n} T σ U t =
      Set.encard {k | k ≤ n ∧ T k ≤ t} -
        Set.encard {k | k ≤ n ∧ departTime φ {j | j ≤ n} T σ U k ≤ t} := by
  have he : {k | k ≤ n ∧ T k ≤ t ∧
      ¬ (IsServed φ {j | j ≤ n} T σ U k ∧ departTime φ {j | j ≤ n} T σ U k ≤ t)} =
      {k | k ≤ n ∧ T k ≤ t} \ {k | k ≤ n ∧ departTime φ {j | j ≤ n} T σ U k ≤ t} := by
    ext k
    by_cases hk : k ≤ n
    · simp only [Set.mem_ofPred_eq,Set.mem_sdiff,hk,true_and,
        finite_customer_isServed φ T σ U n k hk]
    · simp [hk]
  unfold congestion
  simp only [Set.mem_ofPred_eq]
  rw [he]
  apply Set.encard_sdiff
  · intro k hk
    exact ⟨hk.1,(arrival_le_depart_of_served φ _ T σ U hσ k
      (finite_customer_isServed φ T σ U n k hk.1)).trans hk.2⟩
  · exact (Set.finite_Iic n).subset (fun _ hk => hk.1)
lemma finite_departure_count_reordering (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (n : ℕ) (t : ℝ) :
    Set.encard {k | k ≤ n ∧ departTime φ {j | j ≤ n} T σ U k ≤ t} =
      Set.encard {m | m ≤ n ∧ departTime fifo {j | j ≤ n} T (reorderedServices φ T σ U n) U m ≤ t} := by
  let g := rankPerm φ T σ U n
  have he : g '' {m | m ≤ n ∧ departTime fifo {j | j ≤ n} T (reorderedServices φ T σ U n) U m ≤ t} =
      {k | k ≤ n ∧ departTime φ {j | j ≤ n} T σ U k ≤ t} := by
    ext k
    constructor
    · rintro ⟨m,hm,rfl⟩
      exact ⟨rankPerm_le φ T σ U n m hm.1,by
        rw [finite_depart_reordering φ T σ U hT hσ n m hm.1]
        exact hm.2⟩
    · intro hk
      obtain ⟨m,hm,hg⟩ := finite_rank_preimage φ T σ U n k hk.1
      refine ⟨m,⟨hm,?_⟩,hg⟩
      rw [← finite_depart_reordering φ T σ U hT hσ n m hm,hg]
      exact hk.2
  rw [← he]
  exact (rankPerm_fixed_beyond φ T σ U n).1.1.encard_image _
lemma finite_congestion_reordering (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (n : ℕ) (t : ℝ) :
    congestion φ {k | k ≤ n} T σ U t =
      congestion fifo {k | k ≤ n} T (reorderedServices φ T σ U n) U t := by
  rw [finite_congestion_subtraction φ T σ U hσ n t,
    finite_congestion_subtraction fifo T (reorderedServices φ T σ U n) U (fun k => hσ _) n t,
    finite_departure_count_reordering φ T σ U hT hσ n t]
end InterchangeFiniteCongestion
#print axioms InterchangeFiniteCongestion.arrival_le_depart_of_served
#print axioms InterchangeFiniteCongestion.finite_congestion_subtraction
#print axioms InterchangeFiniteCongestion.finite_departure_count_reordering
#print axioms InterchangeFiniteCongestion.finite_congestion_reordering

set_option autoImplicit false
open PalmQueueing.Ordering InterchangePermutation InterchangeFiniteTimes InterchangeClock
open scoped Classical
namespace InterchangeFiniteResidual
lemma finite_residual_summand_reordering (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (n m : ℕ) (hm : m ≤ n) :
    (if IsServed φ {k | k ≤ n} T σ U (rankPerm φ T σ U n m) ∧
      beginTime φ {k | k ≤ n} T σ U (rankPerm φ T σ U n m) ≤ T n ∧
      T n < departTime φ {k | k ≤ n} T σ U (rankPerm φ T σ U n m)
    then departTime φ {k | k ≤ n} T σ U (rankPerm φ T σ U n m)-T n else 0) =
    (if IsServed fifo {k | k ≤ n} T (reorderedServices φ T σ U n) U m ∧
      beginTime fifo {k | k ≤ n} T (reorderedServices φ T σ U n) U m ≤ T n ∧
      T n < departTime fifo {k | k ≤ n} T (reorderedServices φ T σ U n) U m
    then departTime fifo {k | k ≤ n} T (reorderedServices φ T σ U n) U m-T n else 0) := by
  simp only [finite_customer_isServed φ T σ U n _ (rankPerm_le φ T σ U n m hm),
    finite_customer_isServed fifo T (reorderedServices φ T σ U n) U n m hm,
    finite_begin_reordering φ T σ U hT hσ n m hm,
    finite_depart_reordering φ T σ U hT hσ n m hm]
lemma finite_waiting_guard_reordering (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (n m : ℕ) (hm : m ≤ n) :
    (rankPerm φ T σ U n m ∈ {k | k ≤ n} ∧ T (rankPerm φ T σ U n m) ≤ T n ∧
      ¬ (IsServed φ {k | k ≤ n} T σ U (rankPerm φ T σ U n m) ∧
        beginTime φ {k | k ≤ n} T σ U (rankPerm φ T σ U n m) ≤ T n)) ↔
    (m ∈ {k | k ≤ n} ∧ T m ≤ T n ∧
      ¬ (IsServed fifo {k | k ≤ n} T (reorderedServices φ T σ U n) U m ∧
        beginTime fifo {k | k ≤ n} T (reorderedServices φ T σ U n) U m ≤ T n)) := by
  have hg := rankPerm_le φ T σ U n m hm
  simp only [Set.mem_ofPred_eq,hg,hm,hT.monotone hg,hT.monotone hm,
    finite_customer_isServed φ T σ U n _ hg,
    finite_customer_isServed fifo T (reorderedServices φ T σ U n) U n m hm,
    finite_begin_reordering φ T σ U hT hσ n m hm]
lemma finite_residualState_reordering (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (n : ℕ) :
    residualState φ {k | k ≤ n} T σ U n =
      residualState fifo {k | k ≤ n} T (reorderedServices φ T σ U n) U n := by
  classical
  let g := rankPerm φ T σ U n
  have hin : ∀ m ∈ Finset.range (n+1), g m ∈ Finset.range (n+1) := by
    intro m hm
    change rankPerm φ T σ U n m ∈ Finset.range (n+1)
    exact Finset.mem_range.mpr (by have hh := rankPerm_le φ T σ U n m (by have := Finset.mem_range.mp hm; omega); omega)
  have hsurj : ∀ k ∈ Finset.range (n+1), ∃ m, m ∈ Finset.range (n+1) ∧ g m = k := by
    intro k hk
    obtain ⟨m,hm,hg⟩ := finite_rank_preimage φ T σ U n k (by have := Finset.mem_range.mp hk; omega)
    exact ⟨m,Finset.mem_range.mpr (by omega),hg⟩
  apply Prod.ext
  · unfold residualState
    dsimp only
    symm
    apply Finset.sum_nbij g hin (rankPerm_fixed_beyond φ T σ U n).1.1.injOn
    · exact hsurj
    · intro m hm
      exact (finite_residual_summand_reordering φ T σ U hT hσ n m (by have := Finset.mem_range.mp hm; omega)).symm
  · unfold residualState
    dsimp only
    symm
    let sf := (Finset.range (n+1)).filter fun m => m ∈ {k | k ≤ n} ∧ T m ≤ T n ∧
      ¬ (IsServed fifo {k | k ≤ n} T (reorderedServices φ T σ U n) U m ∧
        beginTime fifo {k | k ≤ n} T (reorderedServices φ T σ U n) U m ≤ T n)
    let sp := (Finset.range (n+1)).filter fun k => k ∈ {k | k ≤ n} ∧ T k ≤ T n ∧
      ¬ (IsServed φ {k | k ≤ n} T σ U k ∧ beginTime φ {k | k ≤ n} T σ U k ≤ T n)
    have hmap : sf.val.map (reorderedServices φ T σ U n) = sp.val.map σ := by
      apply Multiset.map_eq_map_of_bij_of_nodup _ _ sf.nodup sp.nodup (fun m _ => g m)
      · intro m hm
        change m ∈ sf at hm
        dsimp only [sf] at hm
        change g m ∈ sp
        dsimp only [sp]
        obtain ⟨hr,hwait⟩ := Finset.mem_filter.mp hm
        apply Finset.mem_filter.mpr
        exact ⟨hin m hr,(finite_waiting_guard_reordering φ T σ U hT hσ n m (by have := Finset.mem_range.mp hr; omega)).mpr hwait⟩
      · intro m hm r hr he
        exact (rankPerm_fixed_beyond φ T σ U n).1.1 he
      · intro k hk
        change k ∈ sp at hk
        dsimp only [sp] at hk
        obtain ⟨hr,hwait⟩ := Finset.mem_filter.mp hk
        obtain ⟨m,hm,hg⟩ := hsurj k hr
        refine ⟨m,?_,hg⟩
        change m ∈ sf
        dsimp only [sf]
        apply Finset.mem_filter.mpr
        refine ⟨hm,?_⟩
        apply (finite_waiting_guard_reordering φ T σ U hT hσ n m (by have := Finset.mem_range.mp hm; omega)).mp
        change rankPerm φ T σ U n m = k at hg
        rw [hg]
        exact hwait
      · intro m hm
        rfl
    convert hmap using 2 <;> apply congrArg Finset.val <;> ext k <;> simp only [sf,sp,Finset.mem_filter]
end InterchangeFiniteResidual
#print axioms InterchangeFiniteResidual.finite_residual_summand_reordering
#print axioms InterchangeFiniteResidual.finite_waiting_guard_reordering
#print axioms InterchangeFiniteResidual.finite_residualState_reordering

set_option autoImplicit false
open PalmQueueing.Ordering InterchangeEvents InterchangeServiceRank InterchangeFullProjection InterchangePrefixStep InterchangeFiniteCongestion InterchangeFiniteResidual InterchangeClock
namespace InterchangeFullEqualities
open scoped Classical
lemma times_eq_of_started (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (n k : ℕ)
    (hk : IsServed φ Set.univ T σ U k ∧ beginTime φ Set.univ T σ U k ≤ T n) :
    beginTime φ Set.univ T σ U k = beginTime φ {j | j ≤ n} T σ U k ∧
    departTime φ Set.univ T σ U k = departTime φ {j | j ≤ n} T σ U k := by
  obtain ⟨m,hm,ht⟩ := (started_by_iff φ Set.univ T σ U k (T n)).mp hk
  have hf := (rank_event_prefix_iff φ T σ U hT hσ n k m (T n) le_rfl).mp ⟨hm,ht⟩
  have hs := full_run_eq_prefix_of_epoch_le φ T σ U hT hσ n m ht
  have hb : beginTime φ Set.univ T σ U k = beginTime φ {j | j ≤ n} T σ U k := by
    rw [beginTime_eq_epoch_of_servedAt φ _ T σ U k m hm,
      beginTime_eq_epoch_of_servedAt φ _ T σ U k m hf.1,hs,epoch_prefix_eq T n _ hf.1.1]
  exact ⟨hb,by simp only [departTime,hb]⟩
lemma congestion_eq_prefix (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (n : ℕ) (t : ℝ) (ht : t ≤ T n) :
    congestion φ Set.univ T σ U t = congestion φ {j | j ≤ n} T σ U t := by
  unfold congestion
  congr 1
  ext k
  simp only [Set.mem_ofPred_eq,Set.mem_univ,true_and]
  rw [departed_prefix_iff φ T σ U hT hσ n k t ht]
  constructor
  · intro hk
    exact ⟨hT.le_iff_le.mp (hk.1.trans ht),hk⟩
  · intro hk
    exact hk.2
lemma residual_summand_eq_prefix (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (n k : ℕ) :
    (if IsServed φ Set.univ T σ U k ∧ beginTime φ Set.univ T σ U k ≤ T n ∧ T n < departTime φ Set.univ T σ U k
      then departTime φ Set.univ T σ U k - T n else 0) =
    (if IsServed φ {j | j ≤ n} T σ U k ∧ beginTime φ {j | j ≤ n} T σ U k ≤ T n ∧ T n < departTime φ {j | j ≤ n} T σ U k
      then departTime φ {j | j ≤ n} T σ U k - T n else 0) := by
  by_cases hk : IsServed φ Set.univ T σ U k ∧ beginTime φ Set.univ T σ U k ≤ T n
  · have hf := (started_prefix_iff φ T σ U hT hσ n k (T n) le_rfl).mp hk
    obtain ⟨hb,hd⟩ := times_eq_of_started φ T σ U hT hσ n k hk
    simp only [hk.1,hf.1,true_and,hb,hd]
  · have hf : ¬(IsServed φ {j | j ≤ n} T σ U k ∧ beginTime φ {j | j ≤ n} T σ U k ≤ T n) :=
      fun h => hk ((started_prefix_iff φ T σ U hT hσ n k (T n) le_rfl).mpr h)
    have hg : ¬(IsServed φ Set.univ T σ U k ∧ beginTime φ Set.univ T σ U k ≤ T n ∧ T n < departTime φ Set.univ T σ U k) :=
      fun h => hk ⟨h.1,h.2.1⟩
    have hg' : ¬(IsServed φ {j | j ≤ n} T σ U k ∧ beginTime φ {j | j ≤ n} T σ U k ≤ T n ∧ T n < departTime φ {j | j ≤ n} T σ U k) :=
      fun h => hf ⟨h.1,h.2.1⟩
    simp only [if_neg hg,if_neg hg']
lemma residualState_eq_prefix (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (n : ℕ) :
    residualState φ Set.univ T σ U n = residualState φ {j | j ≤ n} T σ U n := by
  apply Prod.ext
  · unfold residualState
    dsimp only
    apply Finset.sum_congr rfl
    intro k hk
    exact residual_summand_eq_prefix φ T σ U hT hσ n k
  · unfold residualState
    dsimp only
    congr 2
    ext k
    simp only [Finset.mem_filter]
    by_cases hk : k ∈ Finset.range (n+1)
    · have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
      simp only [hk,true_and,Set.mem_univ,Set.mem_ofPred_eq,hkn,
        started_prefix_iff φ T σ U hT hσ n k (T n) le_rfl]
    · simp only [hk,false_and]
lemma full_congestion_reordering (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (n : ℕ) (t : ℝ) (ht : t ≤ T n) :
    congestion φ Set.univ T σ U t = congestion fifo Set.univ T (reorderedServices φ T σ U n) U t := by
  rw [congestion_eq_prefix φ T σ U hT hσ n t ht,
    congestion_eq_prefix fifo T (reorderedServices φ T σ U n) U hT (fun k => hσ _) n t ht]
  exact finite_congestion_reordering φ T σ U hT hσ n t
lemma full_residualState_reordering (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (n : ℕ) :
    residualState φ Set.univ T σ U n = residualState fifo Set.univ T (reorderedServices φ T σ U n) U n := by
  rw [residualState_eq_prefix φ T σ U hT hσ n,
    residualState_eq_prefix fifo T (reorderedServices φ T σ U n) U hT (fun k => hσ _) n]
  exact finite_residualState_reordering φ T σ U hT hσ n
end InterchangeFullEqualities
#print axioms InterchangeFullEqualities.times_eq_of_started
#print axioms InterchangeFullEqualities.congestion_eq_prefix
#print axioms InterchangeFullEqualities.residual_summand_eq_prefix
#print axioms InterchangeFullEqualities.residualState_eq_prefix
#print axioms InterchangeFullEqualities.full_congestion_reordering
#print axioms InterchangeFullEqualities.full_residualState_reordering

set_option autoImplicit false
open MeasureTheory PalmQueueing.Ordering InterchangeCandidate InterchangeFullEqualities InterchangeClock
namespace InterchangeDeterministic
lemma candidate_congestion_original_obligation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : GIGIInput Ω P) (φ : Discipline) :
    ∀ (n : ℕ) (ω : Ω) (t : ℝ), t ≤ A.T n ω →
      congestion φ Set.univ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) t =
        congestion fifo Set.univ (fun k => A.T k ω) (fun k => A.sigma (candidate A φ n ω k) ω) (fun k => A.U k ω) t := by
  intro n ω t ht
  exact full_congestion_reordering φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω)
      (A.T_strictMono ω) (fun k => A.sigma_nonneg k ω) n t ht
lemma candidate_residual_original_obligation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : GIGIInput Ω P) (φ : Discipline) :
    ∀ (n : ℕ) (ω : Ω),
      residualState φ Set.univ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) n =
        residualState fifo Set.univ (fun k => A.T k ω) (fun k => A.sigma (candidate A φ n ω k) ω) (fun k => A.U k ω) n := by
  intro n ω
  exact full_residualState_reordering φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω)
      (A.T_strictMono ω) (fun k => A.sigma_nonneg k ω) n
theorem first_three_original_obligations {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : GIGIInput Ω P) (φ : Discipline) :
    ∃ gam : ℕ → Ω → ℕ → ℕ,
      (∀ (n : ℕ) (ω : Ω), PermFixedBeyond (gam n ω) n) ∧
      (∀ (n : ℕ) (ω : Ω) (t : ℝ), t ≤ A.T n ω →
        congestion φ Set.univ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) t =
          congestion fifo Set.univ (fun k => A.T k ω) (fun k => A.sigma (gam n ω k) ω)
            (fun k => A.U k ω) t) ∧
      (∀ (n : ℕ) (ω : Ω),
        residualState φ Set.univ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) n =
          residualState fifo Set.univ (fun k => A.T k ω) (fun k => A.sigma (gam n ω k) ω)
            (fun k => A.U k ω) n) := by
  exact ⟨candidate A φ,candidate_first_original_obligation P A φ,
    candidate_congestion_original_obligation P A φ,candidate_residual_original_obligation P A φ⟩
end InterchangeDeterministic
#print axioms InterchangeDeterministic.candidate_congestion_original_obligation
#print axioms InterchangeDeterministic.candidate_residual_original_obligation
#print axioms InterchangeDeterministic.first_three_original_obligations

set_option autoImplicit false
open PalmQueueing.Ordering
namespace InterchangeMask
lemma masked_services_eq (s : SchedState) (σ σ' : ℕ → ℝ)
    (hσ : ∀ k ∈ s.served, σ k = σ' k) :
    (fun k => if k ∈ s.served then σ k else 0) =
      (fun k => if k ∈ s.served then σ' k else 0) := by
  funext k
  by_cases hk : k ∈ s.served
  · simp only [hk,↓reduceIte,hσ k hk]
  · simp only [hk,↓reduceIte]
lemma pick_eq_of_revealed_services (φ : Discipline) (cust : Set ℕ) (T U : ℕ → ℝ)
    (s : SchedState) (σ σ' : ℕ → ℝ) (hσ : ∀ k ∈ s.served, σ k = σ' k) :
    pick φ cust T σ U s = pick φ cust T σ' U s := by
  unfold pick
  rw [masked_services_eq s σ σ' hσ]
lemma step_eq_of_revealed_and_selected_services (φ : Discipline) (cust : Set ℕ) (T U : ℕ → ℝ)
    (s : SchedState) (σ σ' : ℕ → ℝ) (hσ : ∀ k ∈ s.served, σ k = σ' k)
    (hp : σ (pick φ cust T σ U s) = σ' (pick φ cust T σ U s)) :
    step φ cust T σ U s = step φ cust T σ' U s := by
  have he := pick_eq_of_revealed_services φ cust T U s σ σ' hσ
  unfold step
  split_ifs
  · rw [← he,hp]
  · rfl
end InterchangeMask
#print axioms InterchangeMask.masked_services_eq
#print axioms InterchangeMask.pick_eq_of_revealed_services
#print axioms InterchangeMask.step_eq_of_revealed_and_selected_services

set_option autoImplicit false
open PalmQueueing.Ordering InterchangeFiniteRun InterchangePermutation InterchangeClock InterchangeMask
namespace InterchangeInjective
lemma rankPerm_eq_run_get (φ : Discipline) (T σ U : ℕ → ℝ) (n m r : ℕ)
    (hm : m ≤ n+1) (hr : r < m) :
    rankPerm φ T σ U n r = (run φ {k | k ≤ n} T σ U m).served.get
      ⟨r,by rw [finite_run_length φ T σ U n m hm]; exact hr⟩ := by
  have hrn : r ≤ n := by omega
  rw [rankPerm_get φ T σ U n r hrn]
  have hp := finite_run_prefix φ T σ U n m (n+1) hm le_rfl
  exact (hp.getElem (by rw [finite_run_length φ T σ U n m hm]; exact hr)).symm
lemma revealed_services_eq (φ : Discipline) (T σ σ' U : ℕ → ℝ) (n m : ℕ)
    (hm : m ≤ n+1)
    (hh : (run φ {k | k ≤ n} T σ U m).served = (run φ {k | k ≤ n} T σ' U m).served)
    (he : reorderedServices φ T σ U n = reorderedServices φ T σ' U n) :
    ∀ k ∈ (run φ {k | k ≤ n} T σ U m).served, σ k = σ' k := by
  intro k hk
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hk
  have hir : (i : ℕ) < m := by
    have hh' := i.isLt
    have hlen := finite_run_length φ T σ U n m hm
    omega
  have hp : (run φ {k | k ≤ n} T σ U m).served.IsPrefix (run φ {k | k ≤ n} T σ' U m).served := by
    simpa only [hh] using (List.prefix_refl (run φ {k | k ≤ n} T σ' U m).served)
  have hg1 : rankPerm φ T σ U n i = k := (rankPerm_eq_run_get φ T σ U n m i hm hir).trans hi
  have hg2 : rankPerm φ T σ' U n i = k :=
    (rankPerm_eq_run_get φ T σ' U n m i hm hir).trans ((hp.getElem i.isLt).symm.trans hi)
  have hval := congrFun he (i : ℕ)
  change σ (rankPerm φ T σ U n i) = σ' (rankPerm φ T σ' U n i) at hval
  rwa [hg1,hg2] at hval
lemma finite_runs_eq_of_reordered_eq (φ : Discipline) (T σ σ' U : ℕ → ℝ) (n m : ℕ)
    (hm : m ≤ n+1) (he : reorderedServices φ T σ U n = reorderedServices φ T σ' U n) :
    run φ {k | k ≤ n} T σ U m = run φ {k | k ≤ n} T σ' U m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hmn : m ≤ n := by omega
    have hs := ih (by omega)
    have hσ := revealed_services_eq φ T σ σ' U n m (by omega) (congrArg SchedState.served hs) he
    have hp := pick_eq_of_revealed_services φ {k | k ≤ n} T U (run φ {k | k ≤ n} T σ U m) σ σ' hσ
    have hg : rankPerm φ T σ U n m = rankPerm φ T σ' U n m := by
      simp only [rankPerm,hmn,↓reduceIte]
      rw [← hs]
      exact hp
    have hval := congrFun he m
    change σ (rankPerm φ T σ U n m) = σ' (rankPerm φ T σ' U n m) at hval
    rw [← hg] at hval
    have hselected : σ (pick φ {k | k ≤ n} T σ U (run φ {k | k ≤ n} T σ U m)) =
        σ' (pick φ {k | k ≤ n} T σ U (run φ {k | k ≤ n} T σ U m)) := by
      simpa only [rankPerm,hmn,↓reduceIte] using hval
    rw [run,run,← hs]
    exact step_eq_of_revealed_and_selected_services φ {k | k ≤ n} T U _ σ σ' hσ hselected
lemma rankPerm_eq_of_reordered_eq (φ : Discipline) (T σ σ' U : ℕ → ℝ) (n : ℕ)
    (he : reorderedServices φ T σ U n = reorderedServices φ T σ' U n) :
    rankPerm φ T σ U n = rankPerm φ T σ' U n := by
  funext k
  by_cases hk : k ≤ n
  · have hs := finite_runs_eq_of_reordered_eq φ T σ σ' U n (k+1) (by omega) he
    have hh := congrArg SchedState.served hs
    have hm : k < k+1 := by omega
    have hp : (run φ {j | j ≤ n} T σ U (k+1)).served.IsPrefix
        (run φ {j | j ≤ n} T σ' U (k+1)).served := by
      simpa only [hh] using (List.prefix_refl (run φ {j | j ≤ n} T σ' U (k+1)).served)
    rw [rankPerm_eq_run_get φ T σ U n (k+1) k (by omega) hm,
      rankPerm_eq_run_get φ T σ' U n (k+1) k (by omega) hm]
    exact hp.getElem (by rw [finite_run_length φ T σ U n (k+1) (by omega)]; omega)
  · simp only [rankPerm,hk,↓reduceIte]
lemma reorderedServices_injective (φ : Discipline) (T U : ℕ → ℝ) (n : ℕ) :
    Function.Injective (fun σ => reorderedServices φ T σ U n) := by
  intro σ σ' he
  have hg := rankPerm_eq_of_reordered_eq φ T σ σ' U n he
  funext k
  obtain ⟨r,hr⟩ := (rankPerm_fixed_beyond φ T σ U n).1.2 k
  have hval := congrFun he r
  change σ (rankPerm φ T σ U n r) = σ' (rankPerm φ T σ' U n r) at hval
  rw [← hg,hr] at hval
  exact hval
end InterchangeInjective
#print axioms InterchangeInjective.rankPerm_eq_run_get
#print axioms InterchangeInjective.revealed_services_eq
#print axioms InterchangeInjective.finite_runs_eq_of_reordered_eq
#print axioms InterchangeInjective.rankPerm_eq_of_reordered_eq
#print axioms InterchangeInjective.reorderedServices_injective

set_option autoImplicit false
open MeasureTheory PalmQueueing.Ordering
namespace InterchangeMeasurable
open scoped Classical
instance historyMeasurableSpace : MeasurableSpace (List ℕ) := ⊤
instance historyMeasurableSingletonClass : MeasurableSingletonClass (List ℕ) := ⟨fun _ => trivial⟩
lemma measurable_eval_index {Ω : Type*} [MeasurableSpace Ω]
    (f : ℕ → Ω → ℝ) (hf : ∀ k, Measurable (f k)) (j : Ω → ℕ) (hj : Measurable j) :
    Measurable (fun ω => f (j ω) ω) := by
  have h : Measurable (fun p : ℕ × Ω => f p.1 p.2) :=
    measurable_from_prod_countable_right (fun k => hf k)
  exact h.comp (hj.prodMk measurable_id)
lemma measurable_fixed_epoch {Ω : Type*} [MeasurableSpace Ω]
    (cust : Set ℕ) (T : ℕ → Ω → ℝ) (hT : ∀ k, Measurable (T k))
    (l : List ℕ) (c : Ω → ℝ) (hc : Measurable c) :
    Measurable (fun ω => epoch cust (fun k => T k ω) ⟨l,c ω⟩) := by
  change Measurable (fun ω => max (c ω) (T (sInf {k | k ∈ cust ∧ k ∉ l}) ω))
  exact hc.max (hT _)
lemma measurable_fixed_mask {Ω : Type*} [MeasurableSpace Ω]
    (σ : ℕ → Ω → ℝ) (hσ : ∀ k, Measurable (σ k)) (l : List ℕ) :
    Measurable (fun ω k => if k ∈ l then σ k ω else 0) := by
  apply measurable_pi_iff.mpr
  intro k
  by_cases hk : k ∈ l
  · simpa only [hk,↓reduceIte] using hσ k
  · simp only [hk,↓reduceIte]
    exact measurable_const
lemma measurable_fixed_selection {Ω : Type*} [MeasurableSpace Ω]
    (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → Ω → ℝ)
    (hT : ∀ k, Measurable (T k)) (hσ : ∀ k, Measurable (σ k)) (hU : ∀ k, Measurable (U k))
    (l : List ℕ) (c : Ω → ℝ) (hc : Measurable c) :
    Measurable (fun ω => φ.sel l (epoch cust (fun k => T k ω) ⟨l,c ω⟩)
      (fun k => T k ω) (fun k => if k ∈ l then σ k ω else 0) (fun k => U k ω)) := by
  exact (φ.measurable_sel l).comp
    ((measurable_fixed_epoch cust T hT l c hc).prodMk
      ((measurable_pi_iff.mpr hT).prodMk
        ((measurable_fixed_mask σ hσ l).prodMk (measurable_pi_iff.mpr hU))))
end InterchangeMeasurable
#print axioms InterchangeMeasurable.measurable_eval_index
#print axioms InterchangeMeasurable.measurable_fixed_epoch
#print axioms InterchangeMeasurable.measurable_fixed_mask
#print axioms InterchangeMeasurable.measurable_fixed_selection

set_option autoImplicit false
open MeasureTheory PalmQueueing.Ordering
namespace InterchangeMeasurable
open scoped Classical
lemma measurable_fixed_pick {Ω : Type*} [MeasurableSpace Ω]
    (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → Ω → ℝ)
    (hT : ∀ k, Measurable (T k)) (hσ : ∀ k, Measurable (σ k)) (hU : ∀ k, Measurable (U k))
    (l : List ℕ) (c : Ω → ℝ) (hc : Measurable c) :
    Measurable (fun ω => pick φ cust (fun k => T k ω) (fun k => σ k ω) (fun k => U k ω) ⟨l,c ω⟩) := by
  let e := fun ω => epoch cust (fun k => T k ω) ⟨l,c ω⟩
  let j := fun ω => φ.sel l (e ω) (fun k => T k ω) (fun k => if k ∈ l then σ k ω else 0) (fun k => U k ω)
  have he : Measurable e := measurable_fixed_epoch cust T hT l c hc
  have hj : Measurable j := measurable_fixed_selection φ cust T σ U hT hσ hU l c hc
  have hm : MeasurableSet {ω | j ω ∈ cust ∧ j ω ∉ l} :=
    (Set.to_countable {k : ℕ | k ∈ cust ∧ k ∉ l}).measurableSet.preimage hj
  have hw : MeasurableSet {ω | j ω ∈ waiting cust (fun k => T k ω) ⟨l,c ω⟩} :=
    hm.inter (measurableSet_le (measurable_eval_index T hT j hj) he)
  change Measurable (fun ω => if j ω ∈ waiting cust (fun k => T k ω) ⟨l,c ω⟩ then j ω else sInf {k | k ∈ cust ∧ k ∉ l})
  exact Measurable.ite hw hj measurable_const
lemma measurable_epoch {Ω : Type*} [MeasurableSpace Ω]
    (cust : Set ℕ) (T : ℕ → Ω → ℝ) (hT : ∀ k, Measurable (T k))
    (l : Ω → List ℕ) (hl : Measurable l) (c : Ω → ℝ) (hc : Measurable c) :
    Measurable (fun ω => epoch cust (fun k => T k ω) ⟨l ω,c ω⟩) := by
  have h : Measurable (fun p : List ℕ × Ω => epoch cust (fun k => T k p.2) ⟨p.1,c p.2⟩) :=
    measurable_from_prod_countable_right (fun a => measurable_fixed_epoch cust T hT a c hc)
  exact h.comp (hl.prodMk measurable_id)
lemma measurable_pick {Ω : Type*} [MeasurableSpace Ω]
    (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → Ω → ℝ)
    (hT : ∀ k, Measurable (T k)) (hσ : ∀ k, Measurable (σ k)) (hU : ∀ k, Measurable (U k))
    (l : Ω → List ℕ) (hl : Measurable l) (c : Ω → ℝ) (hc : Measurable c) :
    Measurable (fun ω => pick φ cust (fun k => T k ω) (fun k => σ k ω) (fun k => U k ω) ⟨l ω,c ω⟩) := by
  have h : Measurable (fun p : List ℕ × Ω => pick φ cust (fun k => T k p.2) (fun k => σ k p.2) (fun k => U k p.2) ⟨p.1,c p.2⟩) :=
    measurable_from_prod_countable_right (fun a => measurable_fixed_pick φ cust T σ U hT hσ hU a c hc)
  exact h.comp (hl.prodMk measurable_id)
lemma measurable_step_served {Ω : Type*} [MeasurableSpace Ω]
    (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → Ω → ℝ)
    (hT : ∀ k, Measurable (T k)) (hσ : ∀ k, Measurable (σ k)) (hU : ∀ k, Measurable (U k))
    (l : Ω → List ℕ) (hl : Measurable l) (c : Ω → ℝ) (hc : Measurable c) :
    Measurable (fun ω => (step φ cust (fun k => T k ω) (fun k => σ k ω) (fun k => U k ω) ⟨l ω,c ω⟩).served) := by
  have hn : MeasurableSet {ω | (unserved cust ⟨l ω,c ω⟩).Nonempty} :=
    (Set.to_countable {a : List ℕ | (unserved cust ⟨a,0⟩).Nonempty}).measurableSet.preimage hl
  have hj := measurable_pick φ cust T σ U hT hσ hU l hl c hc
  have ha : Measurable (fun ω => l ω ++ [pick φ cust (fun k => T k ω) (fun k => σ k ω) (fun k => U k ω) ⟨l ω,c ω⟩]) :=
    (measurable_of_countable (fun p : List ℕ × ℕ => p.1 ++ [p.2])).comp (hl.prodMk hj)
  have heq : (fun ω => (step φ cust (fun k => T k ω) (fun k => σ k ω) (fun k => U k ω) ⟨l ω,c ω⟩).served) =
      (fun ω => if (unserved cust ⟨l ω,c ω⟩).Nonempty then l ω ++ [pick φ cust (fun k => T k ω) (fun k => σ k ω) (fun k => U k ω) ⟨l ω,c ω⟩] else l ω) := by
    funext ω
    unfold step
    split_ifs <;> rfl
  rw [heq]
  exact Measurable.ite hn ha hl
lemma measurable_step_free {Ω : Type*} [MeasurableSpace Ω]
    (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → Ω → ℝ)
    (hT : ∀ k, Measurable (T k)) (hσ : ∀ k, Measurable (σ k)) (hU : ∀ k, Measurable (U k))
    (l : Ω → List ℕ) (hl : Measurable l) (c : Ω → ℝ) (hc : Measurable c) :
    Measurable (fun ω => (step φ cust (fun k => T k ω) (fun k => σ k ω) (fun k => U k ω) ⟨l ω,c ω⟩).free) := by
  have hn : MeasurableSet {ω | (unserved cust ⟨l ω,c ω⟩).Nonempty} :=
    (Set.to_countable {a : List ℕ | (unserved cust ⟨a,0⟩).Nonempty}).measurableSet.preimage hl
  have hj := measurable_pick φ cust T σ U hT hσ hU l hl c hc
  have ha := (measurable_epoch cust T hT l hl c hc).add
    (measurable_eval_index σ hσ _ hj)
  have heq : (fun ω => (step φ cust (fun k => T k ω) (fun k => σ k ω) (fun k => U k ω) ⟨l ω,c ω⟩).free) =
      (fun ω => if (unserved cust ⟨l ω,c ω⟩).Nonempty then epoch cust (fun k => T k ω) ⟨l ω,c ω⟩ + σ (pick φ cust (fun k => T k ω) (fun k => σ k ω) (fun k => U k ω) ⟨l ω,c ω⟩) ω else c ω) := by
    funext ω
    unfold step
    split_ifs <;> rfl
  rw [heq]
  exact Measurable.ite hn ha hc
lemma measurable_run_components {Ω : Type*} [MeasurableSpace Ω]
    (φ : Discipline) (cust : Set ℕ) (T σ U : ℕ → Ω → ℝ)
    (hT : ∀ k, Measurable (T k)) (hσ : ∀ k, Measurable (σ k)) (hU : ∀ k, Measurable (U k)) (m : ℕ) :
    Measurable (fun ω => (run φ cust (fun k => T k ω) (fun k => σ k ω) (fun k => U k ω) m).served) ∧
    Measurable (fun ω => (run φ cust (fun k => T k ω) (fun k => σ k ω) (fun k => U k ω) m).free) := by
  induction m with
  | zero => exact ⟨measurable_const,hT 0⟩
  | succ m ih =>
    exact ⟨measurable_step_served φ cust T σ U hT hσ hU _ ih.1 _ ih.2,
      measurable_step_free φ cust T σ U hT hσ hU _ ih.1 _ ih.2⟩
end InterchangeMeasurable
#print axioms InterchangeMeasurable.measurable_fixed_pick
#print axioms InterchangeMeasurable.measurable_epoch
#print axioms InterchangeMeasurable.measurable_pick
#print axioms InterchangeMeasurable.measurable_step_served
#print axioms InterchangeMeasurable.measurable_step_free
#print axioms InterchangeMeasurable.measurable_run_components

set_option autoImplicit false
open MeasureTheory PalmQueueing.Ordering InterchangeCandidate InterchangeClock
namespace InterchangeMeasurable
lemma measurable_rankPerm_coordinate {Ω : Type*} [MeasurableSpace Ω]
    (φ : Discipline) (T σ U : ℕ → Ω → ℝ)
    (hT : ∀ k, Measurable (T k)) (hσ : ∀ k, Measurable (σ k)) (hU : ∀ k, Measurable (U k)) (n k : ℕ) :
    Measurable (fun ω => rankPerm φ (fun j => T j ω) (fun j => σ j ω) (fun j => U j ω) n k) := by
  by_cases hk : k ≤ n
  · simp only [rankPerm,hk,↓reduceIte]
    have hr := measurable_run_components φ {j | j ≤ n} T σ U hT hσ hU k
    exact measurable_pick φ {j | j ≤ n} T σ U hT hσ hU _ hr.1 _ hr.2
  · simp only [rankPerm,hk,↓reduceIte]
    exact measurable_const
lemma measurable_reordered_service_array {Ω : Type*} [MeasurableSpace Ω]
    (φ : Discipline) (T σ U : ℕ → Ω → ℝ)
    (hT : ∀ k, Measurable (T k)) (hσ : ∀ k, Measurable (σ k)) (hU : ∀ k, Measurable (U k)) (n : ℕ) :
    Measurable (fun ω => reorderedServices φ (fun j => T j ω) (fun j => σ j ω) (fun j => U j ω) n) := by
  apply measurable_pi_iff.mpr
  intro k
  exact measurable_eval_index σ hσ _ (measurable_rankPerm_coordinate φ T σ U hT hσ hU n k)
lemma measurable_candidate_coordinate {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (A : GIGIInput Ω P) (φ : Discipline) (n k : ℕ) :
    Measurable (fun ω => candidate A φ n ω k) := by
  exact measurable_rankPerm_coordinate φ A.T A.sigma A.U A.measurable_T A.measurable_sigma A.measurable_U n k
lemma measurable_candidate_joint_input {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (A : GIGIInput Ω P) (φ : Discipline) (n : ℕ) :
    Measurable (fun ω => (fun k => A.T k ω, fun k => A.sigma (candidate A φ n ω k) ω)) := by
  apply Measurable.prodMk (measurable_pi_iff.mpr A.measurable_T)
  apply measurable_pi_iff.mpr
  intro k
  exact measurable_eval_index A.sigma A.measurable_sigma _ (measurable_candidate_coordinate A φ n k)
end InterchangeMeasurable
#print axioms InterchangeMeasurable.measurable_rankPerm_coordinate
#print axioms InterchangeMeasurable.measurable_reordered_service_array
#print axioms InterchangeMeasurable.measurable_candidate_coordinate
#print axioms InterchangeMeasurable.measurable_candidate_joint_input

set_option autoImplicit false
open MeasureTheory PalmQueueing.Ordering InterchangeClock InterchangeCandidate InterchangeInjective InterchangeMeasurable
namespace InterchangeJoint
abbrev InputTriple := (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℝ)
noncomputable def reorderInput (φ : Discipline) (n : ℕ) (p : InputTriple) : InputTriple :=
  (p.1,reorderedServices φ p.1 p.2.1 p.2.2 n,p.2.2)
lemma reorderInput_injective (φ : Discipline) (n : ℕ) : Function.Injective (reorderInput φ n) := by
  rintro ⟨T,σ,U⟩ ⟨T',σ',U'⟩ h
  have hT : T = T' := congrArg Prod.fst h
  have hU : U = U' := congrArg (fun p : InputTriple => p.2.2) h
  cases hT
  cases hU
  have hσ : σ = σ' := reorderedServices_injective φ T U n
    (congrArg (fun p : InputTriple => p.2.1) h)
  cases hσ
  rfl
lemma reorderInput_measurable (φ : Discipline) (n : ℕ) : Measurable (reorderInput φ n) := by
  have hT : ∀ k, Measurable (fun p : InputTriple => p.1 k) :=
    fun k => (measurable_pi_apply k).comp measurable_fst
  have hσ : ∀ k, Measurable (fun p : InputTriple => p.2.1 k) :=
    fun k => (measurable_pi_apply k).comp (measurable_fst.comp measurable_snd)
  have hU : ∀ k, Measurable (fun p : InputTriple => p.2.2 k) :=
    fun k => (measurable_pi_apply k).comp (measurable_snd.comp measurable_snd)
  have hτ := measurable_reordered_service_array φ
    (fun k (p : InputTriple) => p.1 k) (fun k p => p.2.1 k) (fun k p => p.2.2 k) hT hσ hU n
  exact measurable_fst.prodMk (hτ.prodMk (measurable_snd.comp measurable_snd))
lemma candidate_pair_eq_reorder_projection {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (A : GIGIInput Ω P) (φ : Discipline) (n : ℕ) :
    (fun ω => (fun k => A.T k ω,fun k => A.sigma (candidate A φ n ω k) ω)) =
      (fun ω => ((reorderInput φ n (fun k => A.T k ω,fun k => A.sigma k ω,fun k => A.U k ω)).1,
        (reorderInput φ n (fun k => A.T k ω,fun k => A.sigma k ω,fun k => A.U k ω)).2.1)) := by
  rfl
end InterchangeJoint
#print axioms InterchangeJoint.reorderInput_injective
#print axioms InterchangeJoint.reorderInput_measurable
#print axioms InterchangeJoint.candidate_pair_eq_reorder_projection

set_option autoImplicit false
open MeasureTheory
namespace InterchangePiecewise
lemma map_le_of_injective_piecewise {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ : Measure α) (f : α → α) (hf : Measurable f) (hinj : Function.Injective f)
    (E : ι → Set α) (hE : ∀ i, MeasurableSet (E i))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j))) (hcover : (⋃ i, E i) = Set.univ)
    (e : ι → α ≃ᵐ α) (he : ∀ i, MeasurePreserving (e i) μ μ)
    (hpiece : ∀ i x, x ∈ E i → f x = e i x) : Measure.map f μ ≤ μ := by
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.map_apply hf hB]
  let S : ι → Set α := fun i => E i ∩ f ⁻¹' B
  let J : ι → Set α := fun i => e i '' S i
  have hS : ∀ i, MeasurableSet (S i) := fun i => (hE i).inter (hB.preimage hf)
  have hSd : Pairwise (fun i j => Disjoint (S i) (S j)) := by
    intro i j hij
    exact (hdis hij).mono Set.inter_subset_left Set.inter_subset_left
  have hJ : ∀ i, MeasurableSet (J i) := fun i => (e i).measurableSet_image.mpr (hS i)
  have hJd : Pairwise (fun i j => Disjoint (J i) (J j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro x ⟨y,hy,rfl⟩ ⟨z,hz,hz'⟩
    have hyz : y = z := hinj ((hpiece i y hy.1).trans (hz'.symm.trans (hpiece j z hz.1).symm))
    have hzE : y ∈ E j := hyz.symm ▸ hz.1
    exact Set.disjoint_left.mp (hdis hij) hy.1 hzE
  have hSc : (⋃ i, S i) = f ⁻¹' B := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
      exact hi.2
    · intro hx
      have hall : x ∈ ⋃ i, E i := by rw [hcover]; exact Set.mem_univ _
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hall
      exact Set.mem_iUnion.mpr ⟨i,hi,hx⟩
  have hJsub : (⋃ i, J i) ⊆ B := by
    intro x hx
    obtain ⟨i,y,hy,rfl⟩ := Set.mem_iUnion.mp hx
    rw [← hpiece i y hy.1]
    exact hy.2
  have hmeasure : ∀ i, μ (S i) = μ (J i) := by
    intro i
    have h := (he i).measure_preimage_equiv (J i)
    change μ ((e i) ⁻¹' (e i '' S i)) = μ (J i) at h
    rwa [Set.preimage_image_eq (S i) (e i).injective] at h
  calc
    μ (f ⁻¹' B) = μ (⋃ i, S i) := congrArg μ hSc.symm
    _ = ∑' i, μ (S i) := measure_iUnion hSd hS
    _ = ∑' i, μ (J i) := tsum_congr hmeasure
    _ = μ (⋃ i, J i) := (measure_iUnion hJd hJ).symm
    _ ≤ μ B := measure_mono hJsub
lemma measurePreserving_of_injective_piecewise {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → α) (hf : Measurable f) (hinj : Function.Injective f)
    (E : ι → Set α) (hE : ∀ i, MeasurableSet (E i))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j))) (hcover : (⋃ i, E i) = Set.univ)
    (e : ι → α ≃ᵐ α) (he : ∀ i, MeasurePreserving (e i) μ μ)
    (hpiece : ∀ i x, x ∈ E i → f x = e i x) : MeasurePreserving f μ μ := by
  refine ⟨hf,?_⟩
  apply Measure.eq_of_le_of_measure_univ_eq
  · exact map_le_of_injective_piecewise μ f hf hinj E hE hdis hcover e he hpiece
  · rw [Measure.map_apply hf MeasurableSet.univ,Set.preimage_univ]
end InterchangePiecewise
#print axioms InterchangePiecewise.map_le_of_injective_piecewise
#print axioms InterchangePiecewise.measurePreserving_of_injective_piecewise

set_option autoImplicit false
open MeasureTheory PalmQueueing.Ordering InterchangeJoint InterchangePermutation InterchangeMeasurable InterchangePiecewise
namespace InterchangeBranches
open scoped Classical
noncomputable def rawRank (φ : Discipline) (n : ℕ) (p : InputTriple) : ℕ → ℕ :=
  rankPerm φ p.1 p.2.1 p.2.2 n
noncomputable def prefixExtension (n : ℕ) (π : Equiv.Perm (Fin (n+1))) : Equiv.Perm ℕ :=
  π.viaFintypeEmbedding Fin.valEmbedding
lemma prefixExtension_apply (n : ℕ) (π : Equiv.Perm (Fin (n+1))) (i : Fin (n+1)) :
    prefixExtension n π i = (π i : ℕ) := by
  exact Equiv.Perm.viaFintypeEmbedding_apply_image π Fin.valEmbedding i
lemma prefixExtension_tail (n : ℕ) (π : Equiv.Perm (Fin (n+1))) (k : ℕ) (hk : n < k) :
    prefixExtension n π k = k := by
  apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
  rintro ⟨i,hi⟩
  have hlt := i.isLt
  change (i : ℕ) = k at hi
  omega
noncomputable def rankPermutation (φ : Discipline) (n : ℕ) (p : InputTriple) : Equiv.Perm (Fin (n+1)) :=
  Equiv.ofBijective
    (fun i => ⟨rawRank φ n p i,by
      have hh := rankPerm_le φ p.1 p.2.1 p.2.2 n i (by have := i.isLt; omega)
      exact Nat.lt_succ_of_le hh⟩)
    ⟨by
      intro i j hij
      apply Fin.ext
      exact (rankPerm_fixed_beyond φ p.1 p.2.1 p.2.2 n).1.1 (congrArg Fin.val hij),
    by
      intro k
      obtain ⟨r,hr⟩ := (rankPerm_fixed_beyond φ p.1 p.2.1 p.2.2 n).1.2 k
      have hle : r ≤ n := by
        by_contra hn
        have hh := (rankPerm_fixed_beyond φ p.1 p.2.1 p.2.2 n).2 r (lt_of_not_ge hn)
        have hk := k.isLt
        omega
      exact ⟨⟨r,by omega⟩,Fin.ext hr⟩⟩
lemma rankPermutation_apply (φ : Discipline) (n : ℕ) (p : InputTriple) (i : Fin (n+1)) :
    (rankPermutation φ n p i : ℕ) = rawRank φ n p i := by rfl
lemma rawRank_measurable (φ : Discipline) (n k : ℕ) : Measurable (fun p : InputTriple => rawRank φ n p k) := by
  have hT : ∀ j, Measurable (fun p : InputTriple => p.1 j) :=
    fun j => (measurable_pi_apply j).comp measurable_fst
  have hσ : ∀ j, Measurable (fun p : InputTriple => p.2.1 j) :=
    fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)
  have hU : ∀ j, Measurable (fun p : InputTriple => p.2.2 j) :=
    fun j => (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)
  exact measurable_rankPerm_coordinate φ _ _ _ hT hσ hU n k
noncomputable def branch (φ : Discipline) (n : ℕ) (π : Equiv.Perm (Fin (n+1))) : Set InputTriple :=
  {p | ∀ i : Fin (n+1), rawRank φ n p i = (π i : ℕ)}
lemma branch_measurable (φ : Discipline) (n : ℕ) (π : Equiv.Perm (Fin (n+1))) :
    MeasurableSet (branch φ n π) := by
  simp only [branch,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_eq_fun (rawRank_measurable φ n i) measurable_const
lemma branch_disjoint (φ : Discipline) (n : ℕ) :
    Pairwise (fun π ρ : Equiv.Perm (Fin (n+1)) => Disjoint (branch φ n π) (branch φ n ρ)) := by
  intro π ρ hne
  apply Set.disjoint_left.mpr
  intro p hp hq
  apply hne
  apply Equiv.ext
  intro i
  apply Fin.ext
  exact (hp i).symm.trans (hq i)
lemma branch_cover (φ : Discipline) (n : ℕ) : (⋃ π, branch φ n π) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  apply Set.mem_iUnion.mpr
  refine ⟨rankPermutation φ n p,?_⟩
  intro i
  exact (rankPermutation_apply φ n p i).symm
lemma rawRank_eq_extension_on_branch (φ : Discipline) (n : ℕ) (π : Equiv.Perm (Fin (n+1)))
    (p : InputTriple) (hp : p ∈ branch φ n π) : rawRank φ n p = prefixExtension n π := by
  funext k
  by_cases hk : k ≤ n
  · let i : Fin (n+1) := ⟨k,by omega⟩
    exact (hp i).trans (prefixExtension_apply n π i).symm
  · rw [prefixExtension_tail n π k (lt_of_not_ge hk)]
    simp only [rawRank,rankPerm,hk,↓reduceIte]
noncomputable def serviceEquiv (n : ℕ) (π : Equiv.Perm (Fin (n+1))) : (ℕ → ℝ) ≃ᵐ (ℕ → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : ℕ => ℝ) (prefixExtension n π).symm
lemma serviceEquiv_apply (n : ℕ) (π : Equiv.Perm (Fin (n+1))) (σ : ℕ → ℝ) (k : ℕ) :
    serviceEquiv n π σ k = σ (prefixExtension n π k) := by
  simpa only [serviceEquiv,Equiv.symm_apply_apply] using
    (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ℕ => ℝ) (prefixExtension n π).symm σ (prefixExtension n π k))
noncomputable def jointEquiv (n : ℕ) (π : Equiv.Perm (Fin (n+1))) : InputTriple ≃ᵐ InputTriple :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.refl (ℕ → ℝ))
    (MeasurableEquiv.prodCongr (serviceEquiv n π) (MeasurableEquiv.refl (ℕ → ℝ)))
lemma reorder_eq_jointEquiv_on_branch (φ : Discipline) (n : ℕ) (π : Equiv.Perm (Fin (n+1)))
    (p : InputTriple) (hp : p ∈ branch φ n π) : reorderInput φ n p = jointEquiv n π p := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext k
      change p.2.1 (rawRank φ n p k) = serviceEquiv n π p.2.1 k
      rw [serviceEquiv_apply]
      exact congrArg p.2.1 (congrFun (rawRank_eq_extension_on_branch φ n π p hp) k)
    · rfl
lemma reorderInput_preserving_of_fixed_permutations (φ : Discipline) (n : ℕ)
    (μ : Measure InputTriple) [IsFiniteMeasure μ]
    (he : ∀ π : Equiv.Perm (Fin (n+1)), MeasurePreserving (jointEquiv n π) μ μ) :
    MeasurePreserving (reorderInput φ n) μ μ := by
  exact measurePreserving_of_injective_piecewise μ (reorderInput φ n)
    (reorderInput_measurable φ n) (reorderInput_injective φ n)
    (branch φ n) (branch_measurable φ n) (branch_disjoint φ n) (branch_cover φ n)
    (jointEquiv n) he (reorder_eq_jointEquiv_on_branch φ n)
end InterchangeBranches
#print axioms InterchangeBranches.prefixExtension_apply
#print axioms InterchangeBranches.prefixExtension_tail
#print axioms InterchangeBranches.rankPermutation_apply
#print axioms InterchangeBranches.rawRank_measurable
#print axioms InterchangeBranches.branch_measurable
#print axioms InterchangeBranches.branch_disjoint
#print axioms InterchangeBranches.branch_cover
#print axioms InterchangeBranches.rawRank_eq_extension_on_branch
#print axioms InterchangeBranches.serviceEquiv_apply
#print axioms InterchangeBranches.reorder_eq_jointEquiv_on_branch
#print axioms InterchangeBranches.reorderInput_preserving_of_fixed_permutations

set_option autoImplicit false
open MeasureTheory Measure ProbabilityTheory PalmQueueing.Ordering InterchangeJoint InterchangeBranches InterchangeCandidate
namespace InterchangeInputLaw
noncomputable def inputArrays {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (A : GIGIInput Ω P) (ω : Ω) : InputTriple :=
  (fun k => A.T k ω,fun k => A.sigma k ω,fun k => A.U k ω)
lemma inputArrays_measurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (A : GIGIInput Ω P) :
    Measurable (inputArrays A) := by
  exact (measurable_pi_iff.mpr A.measurable_T).prodMk
    ((measurable_pi_iff.mpr A.measurable_sigma).prodMk (measurable_pi_iff.mpr A.measurable_U))
lemma sigma_array_law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : GIGIInput Ω P) :
    P.map (fun ω k => A.sigma k ω) = infinitePi (fun _ : ℕ => P.map (A.sigma 0)) := by
  rw [ProbabilityTheory.iIndepFun.map_fun_eq_infinitePi_map A.measurable_sigma A.indep_sigma]
  congr 1
  funext k
  exact (A.ident_sigma k).map_eq
lemma input_joint_law_prod {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : GIGIInput Ω P) :
    P.map (inputArrays A) = (P.map (fun ω k => A.T k ω)).prod
      ((P.map (fun ω k => A.sigma k ω)).prod (P.map (fun ω k => A.U k ω))) := by
  have hT := measurable_pi_iff.mpr A.measurable_T
  have hσ := measurable_pi_iff.mpr A.measurable_sigma
  have hU := measurable_pi_iff.mpr A.measurable_U
  have hX : ∀ i : Fin 3, Measurable (fun ω k => ![A.T,A.sigma,A.U] i k ω) := by
    intro i
    fin_cases i
    · exact hT
    · exact hσ
    · exact hU
  have hSU : IndepFun (fun ω k => A.sigma k ω) (fun ω k => A.U k ω) P :=
    A.indep_input.indepFun (i := (1 : Fin 3)) (j := 2) (by decide)
  have hST : IndepFun (fun ω => (fun k => A.sigma k ω,fun k => A.U k ω)) (fun ω k => A.T k ω) P :=
    ProbabilityTheory.iIndepFun.indepFun_prodMk A.indep_input hX (1 : Fin 3) 2 0 (by decide) (by decide)
  change P.map (fun ω => (fun k => A.T k ω,(fun k => A.sigma k ω,fun k => A.U k ω))) = _
  rw [hST.symm.map_prod_eq_prod_map_map hT.aemeasurable (hσ.prodMk hU).aemeasurable,
    hSU.map_prod_eq_prod_map_map hσ.aemeasurable hU.aemeasurable]
lemma fixed_service_preserving {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : GIGIInput Ω P) (n : ℕ) (π : Equiv.Perm (Fin (n+1))) :
    MeasurePreserving (serviceEquiv n π) (P.map (fun ω k => A.sigma k ω)) (P.map (fun ω k => A.sigma k ω)) := by
  have : IsProbabilityMeasure (P.map (A.sigma 0)) := isProbabilityMeasure_map (A.measurable_sigma 0).aemeasurable
  refine ⟨(serviceEquiv n π).measurable_toFun,?_⟩
  rw [sigma_array_law P A]
  exact infinitePi_map_piCongrLeft (fun _ : ℕ => P.map (A.sigma 0)) (prefixExtension n π).symm
lemma fixed_joint_preserving {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : GIGIInput Ω P) (n : ℕ) (π : Equiv.Perm (Fin (n+1))) :
    MeasurePreserving (jointEquiv n π) (P.map (inputArrays A)) (P.map (inputArrays A)) := by
  have : IsProbabilityMeasure (P.map (fun ω k => A.T k ω)) :=
    isProbabilityMeasure_map (measurable_pi_iff.mpr A.measurable_T).aemeasurable
  have : IsProbabilityMeasure (P.map (fun ω k => A.sigma k ω)) :=
    isProbabilityMeasure_map (measurable_pi_iff.mpr A.measurable_sigma).aemeasurable
  have : IsProbabilityMeasure (P.map (fun ω k => A.U k ω)) :=
    isProbabilityMeasure_map (measurable_pi_iff.mpr A.measurable_U).aemeasurable
  rw [input_joint_law_prod P A]
  exact (MeasurePreserving.id (P.map (fun ω k => A.T k ω))).prod
    ((fixed_service_preserving P A n π).prod (MeasurePreserving.id (P.map (fun ω k => A.U k ω))))
lemma reorderInput_inputLaw_preserving {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : GIGIInput Ω P) (φ : Discipline) (n : ℕ) :
    MeasurePreserving (reorderInput φ n) (P.map (inputArrays A)) (P.map (inputArrays A)) := by
  have : IsProbabilityMeasure (P.map (inputArrays A)) := isProbabilityMeasure_map (inputArrays_measurable A).aemeasurable
  exact reorderInput_preserving_of_fixed_permutations φ n _ (fixed_joint_preserving P A n)
lemma candidate_sameInputLaw_original {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : GIGIInput Ω P) (φ : Discipline) (n : ℕ) : SameInputLaw P A.T A.sigma (candidate A φ n) := by
  let pr : InputTriple → (ℕ → ℝ) × (ℕ → ℝ) := fun p => (p.1,p.2.1)
  have hp : Measurable pr := measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hX := inputArrays_measurable A
  have hF := reorderInput_inputLaw_preserving P A φ n
  have hm : Measure.map (pr ∘ reorderInput φ n) (P.map (inputArrays A)) = Measure.map pr (P.map (inputArrays A)) := by
    rw [← Measure.map_map hp hF.measurable,hF.map_eq]
  have he : P.map (fun ω => pr (reorderInput φ n (inputArrays A ω))) = P.map (fun ω => pr (inputArrays A ω)) := by
    calc
      _ = Measure.map (pr ∘ reorderInput φ n) (P.map (inputArrays A)) :=
        (Measure.map_map (hp.comp hF.measurable) hX).symm
      _ = Measure.map pr (P.map (inputArrays A)) := hm
      _ = _ := Measure.map_map hp hX
  unfold SameInputLaw
  rw [candidate_pair_eq_reorder_projection A φ n]
  exact he
end InterchangeInputLaw
#print axioms InterchangeInputLaw.inputArrays_measurable
#print axioms InterchangeInputLaw.sigma_array_law
#print axioms InterchangeInputLaw.input_joint_law_prod
#print axioms InterchangeInputLaw.fixed_service_preserving
#print axioms InterchangeInputLaw.fixed_joint_preserving
#print axioms InterchangeInputLaw.reorderInput_inputLaw_preserving
#print axioms InterchangeInputLaw.candidate_sameInputLaw_original

set_option autoImplicit false
open MeasureTheory PalmQueueing.Ordering InterchangeCandidate InterchangeDeterministic InterchangeInputLaw


set_option autoImplicit false
open Filter PalmQueueing.Ordering InterchangeFiniteRun InterchangePrefixStep InterchangeFullProjection
namespace LimitReorderingPointwise
open scoped Classical
lemma rankPerm_eventually_full_pick (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (hdiv : Tendsto T atTop atTop) (k : ℕ) :
    ∃ N, ∀ n ≥ N, rankPerm φ T σ U n k = pick φ Set.univ T σ U (run φ Set.univ T σ U k) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (hdiv.eventually (eventually_ge_atTop (epoch Set.univ T (run φ Set.univ T σ U k))))
  refine ⟨max N k,?_⟩
  intro n hn
  have hkn : k ≤ n := (le_max_right N k).trans hn
  have ht : epoch Set.univ T (run φ Set.univ T σ U k) ≤ T n :=
    hN n ((le_max_left N k).trans hn)
  have hs := full_run_eq_prefix_of_epoch_le φ T σ U hT hσ n k ht
  have hu := unserved_nonempty_of_short φ T σ U n k
    (by rw [finite_run_length φ T σ U n k (by omega)]; omega)
  have hp : epoch {j | j ≤ n} T (run φ {j | j ≤ n} T σ U k) ≤ T n := by
    rw [hs,epoch_prefix_eq T n _ hu] at ht
    exact ht
  have he : pick φ Set.univ T σ U (run φ Set.univ T σ U k) =
      pick φ {j | j ≤ n} T σ U (run φ {j | j ≤ n} T σ U k) := by
    rw [hs,pick_prefix_eq φ T σ U hT n _ hu hp]
  simpa only [rankPerm,hkn,↓reduceIte] using he.symm
lemma rankPerm_stabilizes (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (hdiv : Tendsto T atTop atTop) (k : ℕ) :
    ∃ N, ∀ n ≥ N, rankPerm φ T σ U n k = rankPerm φ T σ U N k := by
  obtain ⟨N,hN⟩ := rankPerm_eventually_full_pick φ T σ U hT hσ hdiv k
  exact ⟨N,fun n hn => (hN n hn).trans (hN N le_rfl).symm⟩
lemma limitPerm_eq_full_pick (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (hdiv : Tendsto T atTop atTop) (k : ℕ) :
    limitPerm φ T σ U k = pick φ Set.univ T σ U (run φ Set.univ T σ U k) := by
  have hsettle := rankPerm_stabilizes φ T σ U hT hσ hdiv k
  obtain ⟨N,hN⟩ := rankPerm_eventually_full_pick φ T σ U hT hσ hdiv k
  simp only [limitPerm,dif_pos hsettle]
  have hf := Nat.find_spec hsettle
  exact (hf (max (Nat.find hsettle) N) (le_max_left _ _)).symm.trans
    (hN (max (Nat.find hsettle) N) (le_max_right _ _))
end LimitReorderingPointwise
#print axioms LimitReorderingPointwise.rankPerm_eventually_full_pick
#print axioms LimitReorderingPointwise.rankPerm_stabilizes
#print axioms LimitReorderingPointwise.limitPerm_eq_full_pick

set_option autoImplicit false
open Filter MeasureTheory ProbabilityTheory PalmQueueing.Ordering
namespace LimitReorderingArrival
lemma mean_tau_pos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : GIGIInput Ω P)
    (hρ : ∫ ω, A.sigma 0 ω ∂P < ∫ ω, (A.T 1 ω - A.T 0 ω) ∂P) :
    0 < ∫ ω, (A.T 1 ω - A.T 0 ω) ∂P := by
  exact lt_of_le_of_lt (integral_nonneg (A.sigma_nonneg 0)) hρ
lemma arrival_tendsto_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : GIGIInput Ω P)
    (hτint : Integrable (fun ω => A.T 1 ω - A.T 0 ω) P)
    (hρ : ∫ ω, A.sigma 0 ω ∂P < ∫ ω, (A.T 1 ω - A.T 0 ω) ∂P) :
    ∀ᵐ ω ∂P, Tendsto (fun n => A.T n ω) atTop atTop := by
  have hs := strong_law_ae_real (fun k ω => A.T (k + 1) ω - A.T k ω)
    hτint (fun _ _ hij => A.indep_tau.indepFun hij) A.ident_tau
  filter_upwards [hs] with ω hω
  have hp := hω.pos_mul_atTop (mean_tau_pos P A hρ)
    (tendsto_natCast_atTop_atTop (R := ℝ))
  refine tendsto_atTop_mono' atTop ?_ hp
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [div_mul_cancel₀ _ hn0, Finset.sum_range_sub (fun i => A.T i ω) n]
  exact sub_le_self _ (A.T_zero_nonneg ω)
lemma rankPerm_stabilizes_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : GIGIInput Ω P) (φ : Discipline)
    (hτint : Integrable (fun ω => A.T 1 ω - A.T 0 ω) P)
    (hρ : ∫ ω, A.sigma 0 ω ∂P < ∫ ω, (A.T 1 ω - A.T 0 ω) ∂P) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      rankPerm φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) n k =
      rankPerm φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) N k := by
  filter_upwards [arrival_tendsto_ae P A hτint hρ] with ω hω
  exact fun k => LimitReorderingPointwise.rankPerm_stabilizes φ _ _ _
    (A.T_strictMono ω) (fun k => A.sigma_nonneg k ω) hω k
end LimitReorderingArrival
#print axioms LimitReorderingArrival.mean_tau_pos
#print axioms LimitReorderingArrival.arrival_tendsto_ae
#print axioms LimitReorderingArrival.rankPerm_stabilizes_ae

set_option autoImplicit false
open Filter MeasureTheory Measure ProbabilityTheory PalmQueueing.Ordering
open scoped Topology
namespace LimitReorderingLaw
lemma map_eq_of_ae_tendsto {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X] [HasOuterApproxClosed X]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → X) (F : ℕ → Ω → X)
    (hf : AEMeasurable f P) (hF : ∀ n, Measurable (F n)) (ν : Measure X)
    [IsProbabilityMeasure ν] (hlaw : ∀ n, P.map (F n) = ν)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (f ω))) : P.map f = ν := by
  have : IsProbabilityMeasure (P.map f) := isProbabilityMeasure_map hf
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  have hconv := tendsto_integral_of_dominated_convergence (fun _ : Ω => ‖g‖)
    (fun n => (g.continuous.measurable.comp (hF n)).aestronglyMeasurable)
    (integrable_const _) (fun n => Filter.Eventually.of_forall fun ω => g.norm_coe_le_norm (F n ω))
    (hlim.mono fun ω hω => g.continuous.continuousAt.tendsto.comp hω)
  have heq : ∀ n, (∫ ω, g (F n ω) ∂P) = ∫ x, g x ∂ν := by
    intro n
    rw [← hlaw n, integral_map (hF n).aemeasurable g.continuous.aestronglyMeasurable]
  have hconst : Tendsto (fun _ : ℕ => ∫ x, g x ∂ν) atTop (𝓝 (∫ ω, g (f ω) ∂P)) :=
    by simpa only [Function.comp_apply,heq] using hconv
  have hh := tendsto_nhds_unique hconst tendsto_const_nhds
  rw [integral_map hf g.continuous.aestronglyMeasurable]
  exact hh
lemma full_pick_measurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (A : GIGIInput Ω P) (φ : Discipline) (k : ℕ) :
    Measurable (fun ω => pick φ Set.univ (fun j => A.T j ω) (fun j => A.sigma j ω)
      (fun j => A.U j ω) (run φ Set.univ (fun j => A.T j ω) (fun j => A.sigma j ω)
        (fun j => A.U j ω) k)) := by
  have hr := InterchangeMeasurable.measurable_run_components φ Set.univ A.T A.sigma A.U
    A.measurable_T A.measurable_sigma A.measurable_U k
  exact InterchangeMeasurable.measurable_pick φ Set.univ A.T A.sigma A.U
    A.measurable_T A.measurable_sigma A.measurable_U _ hr.1 _ hr.2
lemma limitPerm_aemeasurable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : GIGIInput Ω P) (φ : Discipline)
    (hdiv : ∀ᵐ ω ∂P, Tendsto (fun n => A.T n ω) atTop atTop) (k : ℕ) :
    AEMeasurable (fun ω => limitPerm φ (fun j => A.T j ω) (fun j => A.sigma j ω)
      (fun j => A.U j ω) k) P := by
  apply (full_pick_measurable A φ k).aemeasurable.congr
  filter_upwards [hdiv] with ω hω
  exact (LimitReorderingPointwise.limitPerm_eq_full_pick φ _ _ _ (A.T_strictMono ω)
    (fun j => A.sigma_nonneg j ω) hω k).symm
lemma limit_joint_aemeasurable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : GIGIInput Ω P) (φ : Discipline)
    (hdiv : ∀ᵐ ω ∂P, Tendsto (fun n => A.T n ω) atTop atTop) :
    AEMeasurable (fun ω => (fun k => A.T k ω, fun k => A.sigma
      (limitPerm φ (fun j => A.T j ω) (fun j => A.sigma j ω) (fun j => A.U j ω) k) ω)) P := by
  apply (measurable_pi_iff.mpr A.measurable_T).aemeasurable.prodMk
  apply aemeasurable_pi_iff.mpr
  intro k
  have hm := InterchangeMeasurable.measurable_eval_index A.sigma A.measurable_sigma _
    (full_pick_measurable A φ k)
  apply hm.aemeasurable.congr
  filter_upwards [hdiv] with ω hω
  rw [LimitReorderingPointwise.limitPerm_eq_full_pick φ _ _ _ (A.T_strictMono ω)
    (fun j => A.sigma_nonneg j ω) hω k]
lemma finite_joint_tendsto_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : GIGIInput Ω P) (φ : Discipline)
    (hdiv : ∀ᵐ ω ∂P, Tendsto (fun n => A.T n ω) atTop atTop) :
    ∀ᵐ ω ∂P, Tendsto (fun n =>
      (fun k => A.T k ω, fun k => A.sigma (InterchangeCandidate.candidate A φ n ω k) ω)) atTop
      (𝓝 (fun k => A.T k ω, fun k => A.sigma
        (limitPerm φ (fun j => A.T j ω) (fun j => A.sigma j ω) (fun j => A.U j ω) k) ω)) := by
  filter_upwards [hdiv] with ω hω
  apply tendsto_const_nhds.prodMk_nhds
  apply tendsto_pi_nhds.mpr
  intro k
  obtain ⟨N,hN⟩ := LimitReorderingPointwise.rankPerm_eventually_full_pick φ
    (fun j => A.T j ω) (fun j => A.sigma j ω) (fun j => A.U j ω)
    (A.T_strictMono ω) (fun j => A.sigma_nonneg j ω) hω k
  apply tendsto_const_nhds.congr'
  apply eventually_atTop.mpr
  refine ⟨N,fun n hn => ?_⟩
  simp only [InterchangeCandidate.candidate,hN n hn,
    LimitReorderingPointwise.limitPerm_eq_full_pick φ _ _ _ (A.T_strictMono ω)
      (fun j => A.sigma_nonneg j ω) hω k]
lemma limit_sameInputLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : GIGIInput Ω P) (φ : Discipline)
    (hdiv : ∀ᵐ ω ∂P, Tendsto (fun n => A.T n ω) atTop atTop) :
    SameInputLaw P A.T A.sigma
      (fun ω => limitPerm φ (fun j => A.T j ω) (fun j => A.sigma j ω) (fun j => A.U j ω)) := by
  have hm : Measurable (fun ω => (fun k => A.T k ω, fun k => A.sigma k ω)) :=
    (measurable_pi_iff.mpr A.measurable_T).prodMk (measurable_pi_iff.mpr A.measurable_sigma)
  have : IsProbabilityMeasure (P.map (fun ω => (fun k => A.T k ω, fun k => A.sigma k ω))) :=
    isProbabilityMeasure_map hm.aemeasurable
  exact map_eq_of_ae_tendsto P _ _ (limit_joint_aemeasurable P A φ hdiv)
    (InterchangeMeasurable.measurable_candidate_joint_input A φ) _
    (InterchangeInputLaw.candidate_sameInputLaw_original P A φ) (finite_joint_tendsto_ae P A φ hdiv)
end LimitReorderingLaw
#print axioms LimitReorderingLaw.map_eq_of_ae_tendsto
#print axioms LimitReorderingLaw.full_pick_measurable
#print axioms LimitReorderingLaw.limitPerm_aemeasurable
#print axioms LimitReorderingLaw.limit_joint_aemeasurable
#print axioms LimitReorderingLaw.finite_joint_tendsto_ae
#print axioms LimitReorderingLaw.limit_sameInputLaw

set_option autoImplicit false
open PalmQueueing.Ordering InterchangeRun InterchangeFullProjection InterchangeFifo
open InterchangeServiceRank Filter
namespace LimitReorderingTimes
open scoped Classical
lemma fifo_full_pick_of_range (T σ U : ℕ → ℝ) (m : ℕ) (s : SchedState)
    (hl : s.served = List.range m) : pick fifo Set.univ T σ U s = m := by
  have hs : sInf (unserved Set.univ s) = m := by
    simpa only [unserved,Set.mem_univ,true_and,hl] using oldest_not_range m
  have hw : m ∈ waiting Set.univ T s := by
    refine ⟨⟨Set.mem_univ _,?_⟩,?_⟩
    · rw [hl]; simp
    · rw [epoch,hs]; exact le_max_right _ _
  have hsel : fifo.sel s.served (epoch Set.univ T s) T
      (fun k => if k ∈ s.served then σ k else 0) U = m := by
    change sInf {k : ℕ | k ∉ s.served} = m
    rw [hl]; exact oldest_not_range m
  unfold pick
  simp only [hsel,hw,↓reduceIte]
lemma fifo_full_served_range (T σ U : ℕ → ℝ) (m : ℕ) :
    (run fifo Set.univ T σ U m).served = List.range m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [run,step,if_pos (full_unserved_nonempty _),
      fifo_full_pick_of_range T σ U m _ ih,ih,List.range_succ]
lemma full_free_clock (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (hdiv : Tendsto T atTop atTop) (m : ℕ) :
    (run φ Set.univ T σ U m).free =
      (run fifo Set.univ T (fun k => σ (limitPerm φ T σ U k)) U m).free := by
  let τ := fun k => σ (limitPerm φ T σ U k)
  have hτ : ∀ k, 0 ≤ τ k := fun k => hσ _
  induction m with
  | zero => rfl
  | succ m ih =>
    have hp := fifo_full_pick_of_range T τ U m _ (fifo_full_served_range T τ U m)
    have hg := LimitReorderingPointwise.limitPerm_eq_full_pick φ T σ U hT hσ hdiv m
    change (run φ Set.univ T σ U (m+1)).free = (run fifo Set.univ T τ U (m+1)).free
    rw [run,step,if_pos (full_unserved_nonempty _),run,step,if_pos (full_unserved_nonempty _)]
    change epoch Set.univ T (run φ Set.univ T σ U m) +
        σ (pick φ Set.univ T σ U (run φ Set.univ T σ U m)) =
      epoch Set.univ T (run fifo Set.univ T τ U m) + τ (pick fifo Set.univ T τ U (run fifo Set.univ T τ U m))
    rw [full_epoch_by_rank φ T σ U hT hσ m,full_epoch_by_rank fifo T τ U hT hτ m,hp,ih]
    exact congrArg (fun j => max (run fifo Set.univ T τ U m).free (T m) + σ j) hg.symm
lemma full_epoch_reordering (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (hdiv : Tendsto T atTop atTop) (m : ℕ) :
    epoch Set.univ T (run φ Set.univ T σ U m) =
      epoch Set.univ T (run fifo Set.univ T (fun k => σ (limitPerm φ T σ U k)) U m) := by
  rw [full_epoch_by_rank φ T σ U hT hσ m,
    full_epoch_by_rank fifo T _ U hT (fun k => hσ _) m,full_free_clock φ T σ U hT hσ hdiv m]
lemma limit_servedAt (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (hdiv : Tendsto T atTop atTop) (m : ℕ) :
    ServedAt φ Set.univ T σ U (limitPerm φ T σ U m) m := by
  exact ⟨full_unserved_nonempty _,
    (LimitReorderingPointwise.limitPerm_eq_full_pick φ T σ U hT hσ hdiv m).symm⟩
lemma fifo_full_servedAt (T σ U : ℕ → ℝ) (m : ℕ) : ServedAt fifo Set.univ T σ U m m := by
  exact ⟨full_unserved_nonempty _,fifo_full_pick_of_range T σ U m _ (fifo_full_served_range T σ U m)⟩
lemma limit_begin_depart (φ : Discipline) (T σ U : ℕ → ℝ)
    (hT : StrictMono T) (hσ : ∀ k, 0 ≤ σ k) (hdiv : Tendsto T atTop atTop) (m : ℕ) :
    beginTime φ Set.univ T σ U (limitPerm φ T σ U m) =
      beginTime fifo Set.univ T (fun k => σ (limitPerm φ T σ U k)) U m ∧
    departTime φ Set.univ T σ U (limitPerm φ T σ U m) =
      departTime fifo Set.univ T (fun k => σ (limitPerm φ T σ U k)) U m := by
  have hφ := limit_servedAt φ T σ U hT hσ hdiv m
  have hψ := fifo_full_servedAt T (fun k => σ (limitPerm φ T σ U k)) U m
  have he := full_epoch_reordering φ T σ U hT hσ hdiv m
  constructor
  · rw [beginTime_eq_epoch_of_servedAt φ Set.univ T σ U _ m hφ,
      beginTime_eq_epoch_of_servedAt fifo Set.univ T _ U m m hψ]
    exact he
  · rw [departTime_eq_epoch_service_of_servedAt φ Set.univ T σ U _ m hφ,
      departTime_eq_epoch_service_of_servedAt fifo Set.univ T _ U m m hψ,he]
end LimitReorderingTimes
#print axioms LimitReorderingTimes.fifo_full_pick_of_range
#print axioms LimitReorderingTimes.fifo_full_served_range
#print axioms LimitReorderingTimes.full_free_clock
#print axioms LimitReorderingTimes.full_epoch_reordering
#print axioms LimitReorderingTimes.limit_servedAt
#print axioms LimitReorderingTimes.fifo_full_servedAt
#print axioms LimitReorderingTimes.limit_begin_depart

set_option autoImplicit false
open MeasureTheory PalmQueueing.Ordering
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : GIGIInput Ω P) (φ : Discipline)
    (hσint : Integrable (A.sigma 0) P) (hτint : Integrable (fun ω => A.T 1 ω - A.T 0 ω) P)
    (hρ : ∫ ω, A.sigma 0 ω ∂P < ∫ ω, (A.T 1 ω - A.T 0 ω) ∂P) :
    (∀ᵐ ω ∂P, ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      rankPerm φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) n k =
        rankPerm φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) N k) ∧
    SameInputLaw P A.T A.sigma
      (fun ω => limitPerm φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω)) ∧
    (∀ᵐ ω ∂P, ∀ n : ℕ,
      beginTime φ Set.univ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω)
          (limitPerm φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) n) =
        beginTime fifo Set.univ (fun k => A.T k ω)
          (fun k => A.sigma
            (limitPerm φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) k) ω)
          (fun k => A.U k ω) n ∧
      departTime φ Set.univ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω)
          (limitPerm φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) n) =
        departTime fifo Set.univ (fun k => A.T k ω)
          (fun k => A.sigma
            (limitPerm φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) k) ω)
          (fun k => A.U k ω) n) := by
  have hdiv := LimitReorderingArrival.arrival_tendsto_ae P A hτint hρ
  refine ⟨LimitReorderingArrival.rankPerm_stabilizes_ae P A φ hτint hρ,
    LimitReorderingLaw.limit_sameInputLaw P A φ hdiv, ?_⟩
  filter_upwards [hdiv] with ω hω
  exact fun n => LimitReorderingTimes.limit_begin_depart φ _ _ _ (A.T_strictMono ω)
    (fun k => A.sigma_nonneg k ω) hω n

#print axioms solution
/-!
# Lemma 4.1.4: the limit reordering (§4.1.3, p.270)
-/

namespace PalmQueueing.Ordering

open MeasureTheory

/-- **Lemma 4.1.4** (p.270). The point process `A'` is equivalent in law to `A`, and such that for
all `n ≥ 0`,

`(4.1.20)  B_{γ(n)}(A, φ) = B_n(A', ψ),   D_{γ(n)}(A, φ) = D_n(A', ψ)`.

`A'` is defined by `A'(C × K) = lim_n A^n(C × K)` (4.1.19), with `γ_n` the permutations of the
proof of Lemma 4.1.3 (`rankPerm`: `γ_n(m)` is the customer served `m`-th under `φ` when the queue
is fed by `A_{[0,n]}`). "If `ρ < 1`, this a.s. limit is well defined since the permutations `γ_n`
are then such that `γ_n(k)` does not depend on `n` after a finite rank"; that claim is the first
conclusion, and `γ = lim_n γ_n` is `limitPerm`, so that `A' = Σ_k δ_{T_k, σ_{γ(k)}}`.

`ρ = E[σ_0] / E[τ_0] < 1`, with `τ_0 = T_1 − T_0`, is stated as `E[σ_0] < E[τ_0]` with both
integrable. -/
example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : GIGIInput Ω P) (φ : Discipline)
    (hσint : Integrable (A.sigma 0) P) (hτint : Integrable (fun ω => A.T 1 ω - A.T 0 ω) P)
    (hρ : ∫ ω, A.sigma 0 ω ∂P < ∫ ω, (A.T 1 ω - A.T 0 ω) ∂P) :
    (∀ᵐ ω ∂P, ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      rankPerm φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) n k =
        rankPerm φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) N k) ∧
    SameInputLaw P A.T A.sigma
      (fun ω => limitPerm φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω)) ∧
    (∀ᵐ ω ∂P, ∀ n : ℕ,
      beginTime φ Set.univ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω)
          (limitPerm φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) n) =
        beginTime fifo Set.univ (fun k => A.T k ω)
          (fun k => A.sigma
            (limitPerm φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) k) ω)
          (fun k => A.U k ω) n ∧
      departTime φ Set.univ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω)
          (limitPerm φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) n) =
        departTime fifo Set.univ (fun k => A.T k ω)
          (fun k => A.sigma
            (limitPerm φ (fun k => A.T k ω) (fun k => A.sigma k ω) (fun k => A.U k ω) k) ω)
          (fun k => A.U k ω) n) := by
  exact solution P A φ hσint hτint hρ

end PalmQueueing.Ordering

#print axioms solution

-- Prove2me | solution 1 for TwoAgentSched.TotalTotal.theorem_9_2_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:16:28.965459+00:00
-- url     : https://prove2.me/submissions/8122ea58-8c1b-49b2-bb93-e381edc112ff

import Mathlib
import Definitions.Def_TwoAgentSched_TotalTotal_Construction

set_option autoImplicit false
open TwoAgentSched.TotalTotal MooreLateJobs.Shared ProjSchedTW.Complexity

section generic
variable {ι : Type*} [DecidableEq ι] (t : ι → ℝ)

lemma ttt_ca_append_left (l₁ l₂ : List ι) (m : ℕ) (hm : m < l₁.length) :
    completionAt t (l₁ ++ l₂) m = completionAt t l₁ m := by
  unfold completionAt
  rw [List.take_append_of_le_length (by omega)]

lemma ttt_ct_append_left (l₁ l₂ : List ι) (x : ι) (hx : x ∈ l₁) :
    completionTime t (l₁ ++ l₂) x = completionTime t l₁ x := by
  unfold completionTime
  rw [List.idxOf_append_of_mem hx]
  exact ttt_ca_append_left t l₁ l₂ _ (List.idxOf_lt_length_iff.mpr hx)

lemma ttt_ct_append_right (l₁ l₂ : List ι) (x : ι) (hx : x ∉ l₁) :
    completionTime t (l₁ ++ l₂) x = (l₁.map t).sum + completionTime t l₂ x := by
  unfold completionTime completionAt
  rw [List.idxOf_append_of_notMem hx, List.take_append]
  have e1 : l₁.take (l₁.length + l₂.idxOf x + 1) = l₁ := List.take_of_length_le (by omega)
  have e3 : l₁.length + l₂.idxOf x + 1 - l₁.length = l₂.idxOf x + 1 := by omega
  rw [e1, e3]
  simp

end generic

namespace TTT

variable {k : ℕ} (p : Fin k → ℕ) (x : Fin k → Bool)

def pr (i : Fin k) : List (Fin k ⊕ Fin k) :=
  if x i then [Sum.inr i, Sum.inl i] else [Sum.inl i, Sum.inr i]

def tt : Fin k ⊕ Fin k → ℝ := Sum.elim (fun i => (p i : ℝ)) (fun i => (p i : ℝ))

lemma sptSeq_eq : sptSeq x = (List.finRange k).flatMap (pr x) := by
  unfold sptSeq pr; rfl

lemma sum_flatMap (L : List (Fin k)) :
    (((L.flatMap (pr x))).map (tt p)).sum = (L.map (fun i => 2 * (p i : ℝ))).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons,
      List.sum_cons]
    unfold pr
    split_ifs <;> simp [tt] <;> ring

lemma mem_take (j i : Fin k) : i ∈ (List.finRange k).take j.val ↔ i.val < j.val := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨n, hn, h⟩
    rw [List.getElem_take, List.getElem_finRange] at h
    have : n < j.val := by simpa using hn
    have h2 : n = i.val := by
      have := congrArg Fin.val h
      simpa using this
    omega
  · intro h
    refine ⟨i.val, by simp; omega, ?_⟩
    rw [List.getElem_take, List.getElem_finRange]
    ext; simp

lemma sum_take (j : Fin k) :
    (((List.finRange k).take j.val).map (fun i => 2 * (p i : ℝ))).sum =
      2 * ∑ i ∈ Finset.univ.filter (fun i : Fin k => i < j), (p i : ℝ) := by
  have hnd : ((List.finRange k).take j.val).Nodup :=
    (List.nodup_finRange k).sublist (List.take_sublist _ _)
  rw [← List.sum_toFinset _ hnd]
  have : ((List.finRange k).take j.val).toFinset = Finset.univ.filter (fun i : Fin k => i < j) := by
    ext i; rw [List.mem_toFinset, mem_take, Finset.mem_filter]; simp
  rw [this, ← Finset.mul_sum]

lemma split (j : Fin k) :
    sptSeq x = ((List.finRange k).take j.val).flatMap (pr x) ++
      (pr x j ++ ((List.finRange k).drop (j.val + 1)).flatMap (pr x)) := by
  rw [sptSeq_eq]
  have h1 : j.val < (List.finRange k).length := by simp
  conv_lhs => rw [← List.take_append_drop j.val (List.finRange k)]
  rw [List.flatMap_append, List.drop_eq_getElem_cons h1, List.flatMap_cons, List.getElem_finRange]
  rfl

lemma ctA (j : Fin k) :
    completionTime (tt p) (sptSeq x) (Sum.inl j) =
      2 * ∑ i ∈ Finset.univ.filter (fun i : Fin k => i < j), (p i : ℝ) + p j +
        (if x j then (p j : ℝ) else 0) := by
  rw [split x j]
  have hn : (Sum.inl j : Fin k ⊕ Fin k) ∉ ((List.finRange k).take j.val).flatMap (pr x) := by
    intro h
    rw [List.mem_flatMap] at h
    obtain ⟨i, hi, hh⟩ := h
    rw [mem_take] at hi
    unfold pr at hh
    split_ifs at hh <;> simp at hh <;> subst hh <;> simp at hi
  rw [ttt_ct_append_right _ _ _ _ hn, sum_flatMap, sum_take]
  have hm : (Sum.inl j : Fin k ⊕ Fin k) ∈ pr x j := by unfold pr; split_ifs <;> simp
  rw [ttt_ct_append_left _ _ _ _ hm]
  unfold pr
  split_ifs with hx
  · simp [completionTime, completionAt, tt]; ring
  · simp [completionTime, completionAt, tt]

lemma ctB (j : Fin k) :
    completionTime (tt p) (sptSeq x) (Sum.inr j) =
      2 * ∑ i ∈ Finset.univ.filter (fun i : Fin k => i < j), (p i : ℝ) + p j +
        (if x j then 0 else (p j : ℝ)) := by
  rw [split x j]
  have hn : (Sum.inr j : Fin k ⊕ Fin k) ∉ ((List.finRange k).take j.val).flatMap (pr x) := by
    intro h
    rw [List.mem_flatMap] at h
    obtain ⟨i, hi, hh⟩ := h
    rw [mem_take] at hi
    unfold pr at hh
    split_ifs at hh <;> simp at hh <;> subst hh <;> simp at hi
  rw [ttt_ct_append_right _ _ _ _ hn, sum_flatMap, sum_take]
  have hm : (Sum.inr j : Fin k ⊕ Fin k) ∈ pr x j := by unfold pr; split_ifs <;> simp
  rw [ttt_ct_append_left _ _ _ _ hm]
  unfold pr
  split_ifs with hx
  · simp [completionTime, completionAt, tt]
  · simp [completionTime, completionAt, tt]; ring

lemma double_sum :
    ∑ j : Fin k, ∑ i ∈ Finset.univ.filter (fun i : Fin k => i < j), (p i : ℝ) =
      (weightedSum p : ℝ) := by
  have h1 : ∀ j : Fin k, ∑ i ∈ Finset.univ.filter (fun i : Fin k => i < j), (p i : ℝ) =
      ∑ i : Fin k, if i < j then (p i : ℝ) else 0 := by
    intro j; rw [Finset.sum_filter]
  simp_rw [h1]
  rw [Finset.sum_comm]
  unfold weightedSum
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : (Finset.univ.filter (fun j : Fin k => i < j)).card = k - (i.val + 1) := by
    have : Finset.univ.filter (fun j : Fin k => i < j) = Finset.Ioi i := by ext; simp
    rw [this, Fin.card_Ioi]; omega
  rw [hc]

end TTT

open TTT in
theorem eq56' {k : ℕ} (p : Fin k → ℕ) (hp : Monotone p) (x : Fin k → Bool) :
    (construction p).sumCA (sptSeq x) =
        (bigP p : ℝ) + 2 * (weightedSum p : ℝ) + (xSum p x : ℝ) ∧
      (construction p).sumCB (sptSeq x) =
        (bigP p : ℝ) + 2 * (weightedSum p : ℝ) + ((bigP p : ℝ) - (xSum p x : ℝ)) := by
  have hp' : (construction p).p = tt p := rfl
  have hA : (construction p).sumCA (sptSeq x) =
      ∑ j : Fin k, (2 * ∑ i ∈ Finset.univ.filter (fun i : Fin k => i < j), (p i : ℝ) + p j +
        (if x j then (p j : ℝ) else 0)) := by
    unfold Instance.sumCA Instance.C
    rw [hp']
    exact Finset.sum_congr rfl (fun j _ => ctA p x j)
  have hB : (construction p).sumCB (sptSeq x) =
      ∑ j : Fin k, (2 * ∑ i ∈ Finset.univ.filter (fun i : Fin k => i < j), (p i : ℝ) + p j +
        (if x j then 0 else (p j : ℝ))) := by
    unfold Instance.sumCB Instance.C
    rw [hp']
    exact Finset.sum_congr rfl (fun j _ => ctB p x j)
  have hx : (xSum p x : ℝ) = ∑ j : Fin k, (if x j then (p j : ℝ) else 0) := by
    unfold xSum; push_cast; simp [Nat.cast_ite]
  have hP : (bigP p : ℝ) = ∑ j : Fin k, (p j : ℝ) := by unfold bigP; push_cast; rfl
  have hD := double_sum p
  have hsplit : ∀ j : Fin k, (if x j then (0 : ℝ) else (p j : ℝ)) =
      (p j : ℝ) - (if x j then (p j : ℝ) else 0) := by
    intro j; split_ifs <;> simp
  constructor
  · rw [hA, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hD, ← hx, ← hP]
    ring
  · rw [hB, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hD]
    simp_rw [hsplit]
    rw [Finset.sum_sub_distrib, ← hx, ← hP]
    ring

theorem fs_spt_total {k : ℕ} (p : Fin k → ℕ) (hp : Monotone p) (x : Fin k → Bool) :
    (construction p).sumCA (sptSeq x) + (construction p).sumCB (sptSeq x) = (bigT p : ℝ) := by
  obtain ⟨h1, h2⟩ := eq56' p hp x
  rw [h1, h2]; unfold bigT; push_cast; ring

section fs
variable {ι : Type*} [DecidableEq ι]

lemma fs_ct_cons_ne (t : ι → ℝ) (y : ι) (R : List ι) (x : ι) (hx : x ≠ y) :
    completionTime t (y :: R) x = t y + completionTime t R x := by
  unfold completionTime completionAt
  rw [List.idxOf_cons_ne _ (Ne.symm hx)]
  simp [List.take_succ_cons]

lemma fs_ct_cons_self (t : ι → ℝ) (y : ι) (R : List ι) :
    completionTime t (y :: R) y = t y := by
  unfold completionTime completionAt
  simp

def fsW : List ℝ → ℝ
  | [] => 0
  | a :: q => ((q.length : ℝ) + 1) * a + fsW q

lemma fs_ct_sum (t : ι → ℝ) : ∀ (l : List ι), l.Nodup →
    ∑ j ∈ l.toFinset, completionTime t l j = fsW (l.map t) := by
  intro l
  induction l with
  | nil => intro _; simp [fsW]
  | cons a l ih =>
    intro hnd
    have han : a ∉ l := (List.nodup_cons.1 hnd).1
    have hndl : l.Nodup := (List.nodup_cons.1 hnd).2
    rw [List.toFinset_cons, Finset.sum_insert (by simpa using han), fs_ct_cons_self]
    have h2 : ∑ j ∈ l.toFinset, completionTime t (a :: l) j =
        ∑ j ∈ l.toFinset, (t a + completionTime t l j) := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      exact fs_ct_cons_ne t a l j (fun e => han (e ▸ List.mem_toFinset.1 hj))
    rw [h2, Finset.sum_add_distrib, ih hndl, Finset.sum_const, List.toFinset_card_of_nodup hndl]
    simp [fsW]
    ring

lemma fsW_ins (a : ℝ) (s : List ℝ) (hs : s.Pairwise (· ≤ ·)) :
    fsW (s.orderedInsert (· ≤ ·) a) ≤ fsW (a :: s) ∧
      ((¬ ∀ b ∈ s, a ≤ b) → fsW (s.orderedInsert (· ≤ ·) a) < fsW (a :: s)) := by
  induction s with
  | nil => simp [fsW]
  | cons b s' ih =>
    have hs' : s'.Pairwise (· ≤ ·) := (List.pairwise_cons.1 hs).2
    have hb : ∀ x ∈ s', b ≤ x := (List.pairwise_cons.1 hs).1
    by_cases hab : a ≤ b
    · rw [List.orderedInsert_cons, if_pos hab]
      refine ⟨le_rfl, fun hcon => absurd (fun x hx => ?_) hcon⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hab
      · exact hab.trans (hb x hx)
    · have hba : b < a := not_le.1 hab
      rw [List.orderedInsert_cons, if_neg hab]
      obtain ⟨ih1, _⟩ := ih hs'
      have hlen : (s'.orderedInsert (· ≤ ·) a).length = s'.length + 1 := List.orderedInsert_length _ _ _
      have e1 : fsW (b :: s'.orderedInsert (· ≤ ·) a) =
          ((s'.length : ℝ) + 2) * b + fsW (s'.orderedInsert (· ≤ ·) a) := by
        simp only [fsW, hlen]; push_cast; ring
      have e2 : fsW (a :: b :: s') = ((s'.length : ℝ) + 2) * a + (((s'.length : ℝ) + 1) * b + fsW s') := by
        simp only [fsW, List.length_cons]; push_cast; ring
      have e3 : fsW (a :: s') = ((s'.length : ℝ) + 1) * a + fsW s' := by
        simp only [fsW]
      rw [e3] at ih1
      constructor
      · rw [e1, e2]; nlinarith
      · intro _; rw [e1, e2]; nlinarith

lemma fsW_sort (q : List ℝ) :
    fsW (q.insertionSort (· ≤ ·)) ≤ fsW q ∧ (¬ q.Pairwise (· ≤ ·) → fsW (q.insertionSort (· ≤ ·)) < fsW q) := by
  induction q with
  | nil => simp [fsW]
  | cons a q ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hs : (q.insertionSort (· ≤ ·)).Pairwise (· ≤ ·) := List.pairwise_insertionSort _ _
    obtain ⟨i1, i2⟩ := fsW_ins a _ hs
    have hlen : (q.insertionSort (· ≤ ·)).length = q.length := List.length_insertionSort _ _
    have e : fsW (a :: q.insertionSort (· ≤ ·)) = ((q.length : ℝ) + 1) * a + fsW (q.insertionSort (· ≤ ·)) := by
      simp only [fsW, hlen]
    have e' : fsW (a :: q) = ((q.length : ℝ) + 1) * a + fsW q := by simp only [fsW]
    rw [List.insertionSort_cons]
    constructor
    · rw [e'] ; rw [e] at i1; linarith
    · intro hnp
      by_cases hq : q.Pairwise (· ≤ ·)
      · have hsq : q.insertionSort (· ≤ ·) = q := List.Pairwise.insertionSort_eq hq
        have hnb : ¬ ∀ b ∈ q.insertionSort (· ≤ ·), a ≤ b := by
          rw [hsq]
          intro hall
          exact hnp (List.pairwise_cons.2 ⟨hall, hq⟩)
        have := i2 hnb
        rw [e'] ; rw [e] at this; linarith
      · have := ih2 hq
        rw [e'] ; rw [e] at i1; linarith

end fs

namespace FS
variable {k : ℕ} (p : Fin k → ℕ)

lemma sptSeq_nodup (x : Fin k → Bool) : (sptSeq x).Nodup := by
  rw [TTT.sptSeq_eq, List.nodup_flatMap]
  refine ⟨fun i _ => ?_, ?_⟩
  · unfold TTT.pr; split_ifs <;> simp
  · refine (List.pairwise_lt_finRange k).imp (fun {i j} hij => ?_)
    intro a ha hb
    unfold TTT.pr at ha hb
    have hij' : i ≠ j := ne_of_lt hij
    split_ifs at ha hb <;> simp at ha hb <;> rcases ha with rfl | rfl <;> rcases hb with h | h <;>
      simp_all

lemma sptSeq_mem (x : Fin k → Bool) (j : Fin k ⊕ Fin k) : j ∈ sptSeq x := by
  rw [TTT.sptSeq_eq, List.mem_flatMap]
  rcases j with i | i
  · exact ⟨i, List.mem_finRange i, by unfold TTT.pr; split_ifs <;> simp⟩
  · exact ⟨i, List.mem_finRange i, by unfold TTT.pr; split_ifs <;> simp⟩

lemma sptSeq_sorted (hp : Monotone p) :
    ((sptSeq (fun _ : Fin k => false)).map (TTT.tt p)).Pairwise (· ≤ ·) := by
  rw [TTT.sptSeq_eq, List.map_flatMap, List.pairwise_flatMap]
  refine ⟨fun i _ => ?_, ?_⟩
  · unfold TTT.pr; simp [TTT.tt]
  · refine (List.pairwise_lt_finRange k).imp (fun {i j} hij => ?_)
    intro a ha b hb
    unfold TTT.pr at ha hb
    simp [TTT.tt] at ha hb
    rw [ha, hb]
    exact_mod_cast hp hij.le

end FS

theorem fs_feasible_spt {k : ℕ} (p : Fin k → ℕ) (hp : Monotone p)
    (l : List (Fin k ⊕ Fin k))
    (hl : (construction p).Meets ((bigT p : ℝ) / 2) ((bigT p : ℝ) / 2) l) :
    (l.map (construction p).p).Pairwise (· ≤ ·) := by
  classical
  obtain ⟨hs, hA, hB⟩ := hl
  have htt : (construction p).p = TTT.tt p := rfl
  rw [htt]
  -- total completion time of l
  have hsum : ∀ m : List (Fin k ⊕ Fin k), IsSchedule Finset.univ m →
      (construction p).sumCA m + (construction p).sumCB m = fsW (m.map (TTT.tt p)) := by
    intro m hm
    have hts : m.toFinset = Finset.univ := by
      ext x; simp [(hm.2 x).2 (Finset.mem_univ x)]
    have := fs_ct_sum (TTT.tt p) m hm.1
    rw [hts] at this
    rw [← this, Fintype.sum_sum_type]
    rfl
  have hl_le : fsW (l.map (TTT.tt p)) ≤ (bigT p : ℝ) := by
    rw [← hsum l hs]; linarith
  have hspt : IsSchedule Finset.univ (sptSeq (fun _ : Fin k => false)) :=
    ⟨FS.sptSeq_nodup _, fun x => ⟨fun _ => Finset.mem_univ _, fun _ => FS.sptSeq_mem _ x⟩⟩
  have hspt_eq : fsW ((sptSeq (fun _ : Fin k => false)).map (TTT.tt p)) = (bigT p : ℝ) := by
    rw [← hsum _ hspt]; exact fs_spt_total p hp _
  -- permutation
  have hperm : l.Perm (sptSeq (fun _ : Fin k => false)) := by
    apply List.perm_of_nodup_nodup_toFinset_eq hs.1 hspt.1
    ext x
    exact ⟨fun _ => List.mem_toFinset.2 ((hspt.2 x).2 (Finset.mem_univ x)),
      fun _ => List.mem_toFinset.2 ((hs.2 x).2 (Finset.mem_univ x))⟩
  have hq : (l.map (TTT.tt p)).Perm ((sptSeq (fun _ : Fin k => false)).map (TTT.tt p)) := hperm.map _
  set q := l.map (TTT.tt p) with hqdef
  set r := (sptSeq (fun _ : Fin k => false)).map (TTT.tt p) with hrdef
  have hsorted : (q.insertionSort (· ≤ ·)).Pairwise (· ≤ ·) := List.pairwise_insertionSort _ _
  have hsperm : (q.insertionSort (· ≤ ·)).Perm r := (List.perm_insertionSort _ _).trans hq
  have hseq : q.insertionSort (· ≤ ·) = r :=
    List.Perm.eq_of_pairwise' hsorted (FS.sptSeq_sorted p hp) hsperm
  by_contra hnp
  have := (fsW_sort q).2 hnp
  rw [hseq, hspt_eq] at this
  linarith


namespace FS2
variable {k : ℕ} (p : Fin k → ℕ)

lemma tt_inl (i : Fin k) : TTT.tt p (Sum.inl i) = (p i : ℝ) := rfl
lemma tt_inr (i : Fin k) : TTT.tt p (Sum.inr i) = (p i : ℝ) := rfl

lemma tt_eq_iff (hp : StrictMono p) (j : Fin k ⊕ Fin k) (i : Fin k) (h : TTT.tt p j = (p i : ℝ)) :
    j = Sum.inl i ∨ j = Sum.inr i := by
  rcases j with j | j
  · left
    have h' : (p j : ℝ) = (p i : ℝ) := h
    have : p j = p i := by exact_mod_cast h'
    rw [hp.injective this]
  · right
    have h' : (p j : ℝ) = (p i : ℝ) := h
    have : p j = p i := by exact_mod_cast h'
    rw [hp.injective this]

lemma struct (hp : StrictMono p) : ∀ (I : List (Fin k)), I.Pairwise (· < ·) →
    ∀ (m : List (Fin k ⊕ Fin k)), m.Nodup →
    m.map (TTT.tt p) = I.flatMap (fun i => [(p i : ℝ), (p i : ℝ)]) →
    ∃ x : Fin k → Bool, m = I.flatMap (TTT.pr x) := by
  intro I
  induction I with
  | nil =>
    intro _ m _ hm
    simp at hm
    exact ⟨fun _ => false, by simp [hm]⟩
  | cons i I' ih =>
    intro hI m hnd hm
    have hI' : I'.Pairwise (· < ·) := (List.pairwise_cons.1 hI).2
    have hlt : ∀ j ∈ I', i < j := (List.pairwise_cons.1 hI).1
    simp only [List.flatMap_cons] at hm
    rcases m with _ | ⟨a, m1⟩
    · simp at hm
    rcases m1 with _ | ⟨b, m'⟩
    · simp at hm
    simp only [List.map_cons, List.cons_append, List.nil_append, List.cons.injEq] at hm
    obtain ⟨ha, hb, hm'⟩ := hm
    have hnd' : (a :: b :: m').Nodup := hnd
    have hab : a ≠ b := fun e => by
      subst e; exact (List.nodup_cons.1 hnd').1 (by simp)
    have hndm' : m'.Nodup := (List.nodup_cons.1 (List.nodup_cons.1 hnd').2).2
    obtain ⟨x', hx'⟩ := ih hI' m' hndm' hm'
    have ha' := tt_eq_iff p hp a i ha
    have hb' := tt_eq_iff p hp b i hb
    refine ⟨Function.update x' i (decide (a = Sum.inr i)), ?_⟩
    simp only [List.flatMap_cons]
    have hcong : I'.flatMap (TTT.pr (Function.update x' i (decide (a = Sum.inr i)))) =
        I'.flatMap (TTT.pr x') := by
      refine List.flatMap_congr (fun j hj => ?_)
      have : j ≠ i := (ne_of_gt (hlt j hj))
      unfold TTT.pr
      rw [Function.update_of_ne this]
    rw [hcong, ← hx']
    have : TTT.pr (Function.update x' i (decide (a = Sum.inr i))) i = [a, b] := by
      unfold TTT.pr
      rw [Function.update_self]
      rcases ha' with rfl | rfl
      · rcases hb' with rfl | rfl
        · exact absurd rfl hab
        · simp
      · rcases hb' with rfl | rfl
        · simp
        · exact absurd rfl hab
    rw [this]; rfl

end FS2

lemma fs_sched {k : ℕ} (x : Fin k → Bool) : IsSchedule Finset.univ (sptSeq x) :=
  ⟨FS.sptSeq_nodup _, fun y => ⟨fun _ => Finset.mem_univ _, fun _ => FS.sptSeq_mem _ y⟩⟩

lemma fs_hget {k : ℕ} (p : Fin k → ℕ) (hlen : (List.ofFn p).length = k)
    (A : Finset (Fin (List.ofFn p).length)) :
    ∑ i ∈ A, (List.ofFn p).get i = ∑ h : Fin k, if (Fin.cast hlen.symm h) ∈ A then p h else 0 := by
  classical
  have h0 : ∑ i ∈ A, (List.ofFn p).get i = ∑ i, if i ∈ A then (List.ofFn p).get i else 0 := by
    rw [← Finset.sum_filter]; congr 1; ext i; simp
  rw [h0]
  refine Fintype.sum_equiv (finCongr hlen) _ _ (fun i => ?_)
  have e : Fin.cast hlen.symm (finCongr hlen i) = i := by ext; simp
  simp only [e, List.get_ofFn]
  rfl

theorem solution {k : ℕ} (p : Fin k → ℕ) (hp : StrictMono p) :
    PartitionYes (List.ofFn p) ↔
      (construction p).RecYes ((bigT p : ℝ) / 2) ((bigT p : ℝ) / 2) := by
  classical
  have hmono : Monotone p := hp.monotone
  have hlen : (List.ofFn p).length = k := List.length_ofFn
  have hT : (bigT p : ℝ) / 2 = (3 / 2 : ℝ) * (bigP p : ℝ) + 2 * (weightedSum p : ℝ) := by
    unfold bigT; push_cast; ring
  have hP : (bigP p : ℝ) = ∑ h : Fin k, (p h : ℝ) := by unfold bigP; push_cast; rfl
  have hxS : ∀ x : Fin k → Bool, (xSum p x : ℝ) = ∑ h : Fin k, (if x h then (p h : ℝ) else 0) := by
    intro x; unfold xSum; push_cast; simp [Nat.cast_ite]
  constructor
  · rintro ⟨A, hA⟩
    rw [fs_hget p hlen A, fs_hget p hlen Aᶜ] at hA
    set x : Fin k → Bool := fun h => decide (Fin.cast hlen.symm h ∈ A) with hx
    have hsum2 : 2 * (xSum p x : ℝ) = (bigP p : ℝ) := by
      have e1 : ∑ h : Fin k, (if Fin.cast hlen.symm h ∈ A then p h else 0) = xSum p x := by
        unfold xSum; simp [hx]
      have e2 : ∑ h : Fin k, (if Fin.cast hlen.symm h ∈ Aᶜ then p h else 0) +
          ∑ h : Fin k, (if Fin.cast hlen.symm h ∈ A then p h else 0) = bigP p := by
        unfold bigP
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun h _ => ?_)
        by_cases hh : Fin.cast hlen.symm h ∈ A <;> simp [hh]
      rw [e1] at hA e2
      have : 2 * xSum p x = bigP p := by omega
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) this
    obtain ⟨h1, h2⟩ := eq56' p hmono x
    refine ⟨sptSeq x, fs_sched x, ?_, ?_⟩
    · rw [h1, hT]; linarith
    · rw [h2, hT]; linarith
  · rintro ⟨l, hl⟩
    have hfs := fs_feasible_spt p hmono l hl
    obtain ⟨hs, hA, hB⟩ := hl
    have hperm : l.Perm (sptSeq (fun _ : Fin k => false)) := by
      apply List.perm_of_nodup_nodup_toFinset_eq hs.1 (fs_sched _).1
      ext y
      exact ⟨fun _ => List.mem_toFinset.2 (((fs_sched (fun _ : Fin k => false)).2 y).2 (Finset.mem_univ y)),
        fun _ => List.mem_toFinset.2 ((hs.2 y).2 (Finset.mem_univ y))⟩
    have hq : (l.map (TTT.tt p)).Perm ((sptSeq (fun _ : Fin k => false)).map (TTT.tt p)) :=
      hperm.map _
    have hqr : l.map (TTT.tt p) = (sptSeq (fun _ : Fin k => false)).map (TTT.tt p) :=
      List.Perm.eq_of_pairwise' hfs (FS.sptSeq_sorted p hmono) hq
    have hr : (sptSeq (fun _ : Fin k => false)).map (TTT.tt p) =
        (List.finRange k).flatMap (fun i => [(p i : ℝ), (p i : ℝ)]) := by
      rw [TTT.sptSeq_eq, List.map_flatMap]
      refine List.flatMap_congr (fun i _ => ?_)
      unfold TTT.pr; simp [TTT.tt]
    obtain ⟨x, hx⟩ := FS2.struct p hp (List.finRange k) (List.pairwise_lt_finRange k) l hs.1
      (hqr.trans hr)
    have hlx : l = sptSeq x := by rw [hx, TTT.sptSeq_eq]
    subst hlx
    obtain ⟨h1, h2⟩ := eq56' p hmono x
    have hA2 : (bigP p : ℝ) + 2 * (weightedSum p : ℝ) + (xSum p x : ℝ) ≤
        (3 / 2 : ℝ) * (bigP p : ℝ) + 2 * (weightedSum p : ℝ) := by
      rw [← hT, ← h1]; exact hA
    have hB2 : (bigP p : ℝ) + 2 * (weightedSum p : ℝ) + ((bigP p : ℝ) - (xSum p x : ℝ)) ≤
        (3 / 2 : ℝ) * (bigP p : ℝ) + 2 * (weightedSum p : ℝ) := by
      rw [← hT, ← h2]; exact hB
    have hsum2 : 2 * xSum p x = bigP p := by
      have : 2 * (xSum p x : ℝ) = (bigP p : ℝ) := by linarith
      exact_mod_cast this
    refine ⟨Finset.univ.filter (fun i : Fin (List.ofFn p).length => x (Fin.cast hlen i)), ?_⟩
    set A := Finset.univ.filter (fun i : Fin (List.ofFn p).length => x (Fin.cast hlen i)) with hAdef
    rw [fs_hget p hlen A, fs_hget p hlen Aᶜ]
    have e1 : ∑ h : Fin k, (if Fin.cast hlen.symm h ∈ A then p h else 0) = xSum p x := by
      unfold xSum
      refine Finset.sum_congr rfl (fun h _ => ?_)
      have : Fin.cast hlen (Fin.cast hlen.symm h) = h := by ext; simp
      simp [hAdef, this]
    have e2 : ∑ h : Fin k, (if Fin.cast hlen.symm h ∈ Aᶜ then p h else 0) +
        ∑ h : Fin k, (if Fin.cast hlen.symm h ∈ A then p h else 0) = bigP p := by
      unfold bigP
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun h _ => ?_)
      by_cases hh : Fin.cast hlen.symm h ∈ A <;> simp [hh]
    rw [e1] at e2 ⊢
    omega

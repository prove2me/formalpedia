-- Prove2me | solution 1 for RoundRobinEq.SubmodularBluff.theorem_3_7
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T10:18:04.714684+00:00
-- url     : https://prove2.me/submissions/ce050422-5683-43be-91df-8cf0234afdcd

import Definitions.Def_RoundRobinEq_CancelableBluff_Setting
import Definitions.Def_RoundRobinEq_SubmodularBluff_Bluff
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Range
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.FinRange
import Definitions.Def_RoundRobinEq_SubmodularBluff_Setting
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_RoundRobinEq_SubmodularBluff_TightInstance
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.Permutation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
noncomputable section

section
open RoundRobinEq.CancelableBluff

namespace S05P070

section Rankings
variable {M : Type*} [Fintype M] [DecidableEq M]

lemma ranking_length {h : List M} (hh : IsRanking h) : h.length = Fintype.card M := by
  have hu : h.toFinset = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro g
    simpa using hh.2 g
  calc
    h.length = h.toFinset.card := (List.toFinset_card_of_nodup hh.1).symm
    _ = Fintype.card M := by rw [hu, Finset.card_univ]

lemma top_mem {h : List M} {A : Finset M} {g : M} (hg : top h A = some g) : g ∈ A := by
  have hp := List.find?_some hg
  simpa using hp

lemma top_exists {h : List M} (hh : IsRanking h) {A : Finset M} (hA : A.Nonempty) :
    ∃ g, top h A = some g := by
  cases hx : top h A with
  | none =>
    obtain ⟨g, hg⟩ := hA
    have hp := List.find?_eq_none.mp hx g (hh.2 g)
    exact False.elim (hp (by simpa using hg))
  | some g => exact ⟨g, rfl⟩

/-- Scanning a noduplicate list past its allocated prefix returns exactly its next entry. -/
lemma top_complement_take (h : List M) (hh : h.Nodup) (t : ℕ) :
    top h (Finset.univ \ (h.take t).toFinset) = h[t]? := by
  by_cases ht : t < h.length
  · rw [List.getElem?_eq_getElem ht]
    apply List.find?_eq_some_iff_getElem.mpr
    have hnot : h[t] ∉ h.take t := by
      intro hm
      obtain ⟨j, hj, heq⟩ := List.mem_take_iff_getElem.mp hm
      have hji : j = t := hh.getElem_inj_iff.mp heq
      omega
    refine ⟨by simpa using hnot, t, ht, rfl, ?_⟩
    intro j hj
    have hm : h[j] ∈ h.take t :=
      List.mem_take_iff_getElem.mpr ⟨j, by omega, rfl⟩
    simpa using hm
  · have htake : h.take t = h := List.take_of_length_le (by omega)
    rw [List.getElem?_eq_none (by omega)]
    apply List.find?_eq_none.mpr
    intro g hg
    simp [htake, hg]

/-- A top choice precedes every other available good in its complete ranking. -/
lemma top_idxOf_le {h : List M} (hh : IsRanking h) {A : Finset M} {g x : M}
    (hg : top h A = some g) (hx : x ∈ A) : h.idxOf g ≤ h.idxOf x := by
  obtain ⟨_, i, hi, hig, hfirst⟩ := List.find?_eq_some_iff_getElem.mp hg
  have hgi : h.idxOf g = i := by
    rw [← hig]
    exact hh.1.idxOf_getElem i hi
  by_contra hle
  have hix : h.idxOf x < i := by omega
  have hxlen := List.idxOf_lt_length_of_mem (hh.2 x)
  have hfalse := hfirst (h.idxOf x) hix
  have hval : h[h.idxOf x] = x := List.getElem_idxOf hxlen
  rw [hval] at hfalse
  have hn : x ∉ A := by simpa using hfalse
  exact hn hx

end Rankings

section Execution
variable {n : ℕ} [NeZero n] {M : Type*} [Fintype M] [DecidableEq M]

lemma allocBefore_succ_union (σ : Fin n → List M) (t : ℕ) :
    allocBefore σ (t + 1) = allocBefore σ t ∪ (pick σ t).toFinset := by
  change (match pick σ t with
    | some g => insert g (allocBefore σ t)
    | none => allocBefore σ t) = _
  cases hp : pick σ t <;> simp [Finset.union_comm]

lemma allocBefore_eq_biUnion (σ : Fin n → List M) (t : ℕ) :
    allocBefore σ t = (Finset.range t).biUnion (fun s => (pick σ s).toFinset) := by
  induction t with
  | zero => simp [allocBefore]
  | succ t ih =>
    rw [allocBefore_succ_union, ih, Finset.range_add_one]
    simp [Finset.union_comm]

lemma mem_allocBefore_iff (σ : Fin n → List M) (t : ℕ) (g : M) :
    g ∈ allocBefore σ t ↔ ∃ s < t, pick σ s = some g := by
  rw [allocBefore_eq_biUnion]
  simp

lemma allocBefore_mono (σ : Fin n → List M) : Monotone (allocBefore σ) := by
  intro s t hst g hg
  obtain ⟨u, hu, hp⟩ := (mem_allocBefore_iff σ s g).mp hg
  exact (mem_allocBefore_iff σ t g).mpr ⟨u, lt_of_lt_of_le hu hst, hp⟩

lemma pick_not_mem_allocBefore (σ : Fin n → List M) {t : ℕ} {g : M}
    (hg : pick σ t = some g) : g ∉ allocBefore σ t := by
  have hm := top_mem hg
  exact (Finset.mem_sdiff.mp hm).2

lemma pick_some_injective (σ : Fin n → List M) {s t : ℕ} {g : M}
    (hs : pick σ s = some g) (ht : pick σ t = some g) : s = t := by
  rcases lt_trichotomy s t with hst | hst | hts
  · exact False.elim ((pick_not_mem_allocBefore σ ht)
      ((mem_allocBefore_iff σ t g).mpr ⟨s, hst, hs⟩))
  · exact hst
  · exact False.elim ((pick_not_mem_allocBefore σ hs)
      ((mem_allocBefore_iff σ s g).mpr ⟨t, hts, ht⟩))

lemma allocBefore_card_le (σ : Fin n → List M) (t : ℕ) : (allocBefore σ t).card ≤ t := by
  induction t with
  | zero => simp [allocBefore]
  | succ t ih =>
    change (match pick σ t with
      | some g => insert g (allocBefore σ t)
      | none => allocBefore σ t).card ≤ t + 1
    cases hp : pick σ t with
    | none => exact le_trans ih (Nat.le_succ t)
    | some g => exact (Finset.card_insert_le g _).trans (Nat.add_le_add_right ih 1)

lemma pick_exists_of_lt (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    {t : ℕ} (ht : t < Fintype.card M) : ∃ g, pick σ t = some g := by
  apply top_exists (hσ (agentAt n t))
  apply Finset.sdiff_nonempty_of_card_lt_card
  simpa using lt_of_le_of_lt (allocBefore_card_le σ t) ht

lemma allocBefore_card (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    (t : ℕ) (ht : t ≤ Fintype.card M) : (allocBefore σ t).card = t := by
  induction t with
  | zero => simp [allocBefore]
  | succ t ih =>
    obtain ⟨g, hg⟩ := pick_exists_of_lt σ hσ (Nat.lt_of_succ_le ht)
    have hnot := pick_not_mem_allocBefore σ hg
    change (match pick σ t with
      | some g => insert g (allocBefore σ t)
      | none => allocBefore σ t).card = t + 1
    rw [hg, Finset.card_insert_of_notMem hnot, ih (Nat.le_of_succ_le ht)]

lemma bluff_allocBefore (h : List M) (hh : h.Nodup) (t : ℕ) :
    allocBefore (RoundRobinEq.SubmodularBluff.bluff (n := n) h) t = (h.take t).toFinset := by
  induction t with
  | zero => simp [allocBefore]
  | succ t ih =>
    rw [allocBefore_succ_union, ih]
    have hp : pick (RoundRobinEq.SubmodularBluff.bluff (n := n) h) t = h[t]? := by
      unfold pick
      rw [ih]
      exact top_complement_take h hh t
    rw [hp, List.take_add_one]
    cases hget : h[t]? <;> simp [hget, Finset.union_comm]

lemma bluff_pick (h : List M) (hh : h.Nodup) (t : ℕ) :
    pick (RoundRobinEq.SubmodularBluff.bluff (n := n) h) t = h[t]? := by
  unfold pick
  rw [bluff_allocBefore h hh]
  exact top_complement_take h hh t

lemma bluff_roundRobin (h : List M) (hh : h.Nodup) (i : Fin n) :
    roundRobin (RoundRobinEq.SubmodularBluff.bluff h) i =
      ((Finset.range (Fintype.card M)).filter (fun t => agentAt n t = i)).biUnion
        (fun t => (h[t]?).toFinset) := by
  unfold roundRobin
  simp_rw [bluff_pick h hh]

lemma bluff_greedyBundle (h : List M) (hh : h.Nodup) (j : ℕ) :
    ((Finset.range j).filter (fun t => agentAt n t = agentAt n j)).biUnion
      (fun t => (pick (RoundRobinEq.SubmodularBluff.bluff (n := n) h) t).toFinset) =
      RoundRobinEq.SubmodularBluff.greedyBundle n h j := by
  unfold RoundRobinEq.SubmodularBluff.greedyBundle
  simp_rw [bluff_pick h hh]

/-- An agent reporting h chooses a good no later than any still available good in h. -/
lemma pick_idxOf_le (σ : Fin n → List M) {h : List M} (hh : IsRanking h)
    {s : ℕ} {g x : M} (hreport : σ (agentAt n s) = h)
    (hg : pick σ s = some g) (hx : x ∉ allocBefore σ s) :
    h.idxOf g ≤ h.idxOf x := by
  apply top_idxOf_le hh (A := Finset.univ \ allocBefore σ s)
  · simpa only [pick, hreport] using hg
  · simp [hx]

lemma pick_mem_take_of_available (σ : Fin n → List M) {h : List M} (hh : IsRanking h)
    {s t : ℕ} {g x : M} (hreport : σ (agentAt n s) = h)
    (hg : pick σ s = some g) (hx : x ∉ allocBefore σ s) (hxt : x ∈ h.take t) :
    g ∈ h.take t := by
  apply (List.mem_take_iff_idxOf_lt (hh.2 g)).mpr
  exact lt_of_le_of_lt (pick_idxOf_le σ hh hreport hg hx)
    ((List.mem_take_iff_idxOf_lt (hh.2 x)).mp hxt)

end Execution
end S05P070
end

section
namespace S05P070

open Finset

lemma actor_times_eq_image (n i r : ℕ) (hn : 0 < n) (hi : i < n) :
    ((range (r * n + i + 1)).filter (fun t => t % n = i)) =
      (range (r + 1)).image (fun a => a * n + i) := by
  ext t
  simp only [mem_filter, mem_range, mem_image]
  constructor
  · rintro ⟨ht, hmod⟩
    refine ⟨t / n, ?_, ?_⟩
    · apply (Nat.div_lt_iff_lt_mul hn).2
      nlinarith
    · have hd := Nat.mod_add_div' t n
      omega
  · rintro ⟨a, ha, rfl⟩
    constructor
    · nlinarith
    · simp [Nat.add_mod, Nat.mod_eq_of_lt hi]

lemma actor_times_card (n i r : ℕ) (hn : 0 < n) (hi : i < n) :
    ((range (r * n + i + 1)).filter (fun t => t % n = i)).card = r + 1 := by
  rw [actor_times_eq_image n i r hn hi, card_image_of_injective]
  · simp
  · intro a b hab
    exact Nat.eq_of_mul_eq_mul_right hn (Nat.add_right_cancel hab)

/-- Against opponents who always choose earlier ranked available goods, the deviator
can acquire at most `j` goods from the first `j*n+i` positions of the common ranking.
Here `p t` is the common-ranking position of the good allocated at time `t`, and `A`
is the set of deviator times whose goods lie in that prefix.  This form isolates the
finite combinatorial coupling from the concrete recursive execution. -/
theorem scheduled_prefix_card_le (n i j m : ℕ) (hn : 0 < n) (hi : i < n)
    (p : ℕ → ℕ) (A : Finset ℕ)
    (ha : ∀ t ∈ A, t < m ∧ t % n = i ∧ p t < j * n + i)
    (hinj : ∀ a < m, ∀ b < m, p a = p b → a = b)
    (hopp : ∀ t ∈ A, ∀ s < t, s % n ≠ i → p s ≤ p t) :
    A.card ≤ j := by
  classical
  by_cases hA : A.Nonempty
  · let t := A.max' hA
    have htA : t ∈ A := max'_mem A hA
    obtain ⟨htm, htmod, htp⟩ := ha t htA
    let r := t / n
    have ht : t = r * n + i := by
      dsimp [r]
      have hd := Nat.mod_add_div' t n
      omega
    let R := range (t + 1)
    let own := R.filter (fun s => s % n = i)
    let other := R \ own
    have hown : own.card = r + 1 := by
      dsimp [own, R]
      rw [ht]
      exact actor_times_card n i r hn hi
    have hownR : own ⊆ R := filter_subset _ _
    have hother : other.card + own.card = t + 1 := by
      simpa [other, R] using card_sdiff_add_card_eq_card hownR
    have hAsub : A ⊆ own := by
      intro s hs
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (le_max' A s hs)),
        (ha s hs).2.1⟩
    have hAc : A.card ≤ r + 1 := hown ▸ card_le_card hAsub
    have hdis : Disjoint A other := by
      apply disjoint_left.mpr
      intro s hs hsother
      exact (mem_sdiff.mp hsother).2 (hAsub hs)
    have hCR : A ∪ other ⊆ R := by
      exact union_subset (hAsub.trans hownR) sdiff_subset
    have hsub : (A ∪ other).image p ⊆ range (j * n + i) := by
      intro x hx
      obtain ⟨s, hs, rfl⟩ := mem_image.mp hx
      apply mem_range.mpr
      rcases mem_union.mp hs with hsA | hsother
      · exact (ha s hsA).2.2
      · obtain ⟨hsR, hsown⟩ := mem_sdiff.mp hsother
        have hsne : s % n ≠ i := by
          intro heq
          exact hsown (mem_filter.mpr ⟨hsR, heq⟩)
        have hst : s < t := by
          have hsle : s < t + 1 := mem_range.mp hsR
          have hsnt : s ≠ t := by
            intro heq
            exact hsne (heq ▸ htmod)
          omega
        exact lt_of_le_of_lt (hopp t htA s hst hsne) htp
    have hinjC : Set.InjOn p ↑(A ∪ other) := by
      intro a haC b hbC hab
      have haR := mem_range.mp (hCR haC)
      have hbR := mem_range.mp (hCR hbC)
      exact hinj a (by omega) b (by omega) hab
    have hbound : A.card + other.card ≤ j * n + i := by
      have hc := card_le_card hsub
      rw [card_image_of_injOn hinjC, card_union_of_disjoint hdis, card_range] at hc
      exact hc
    by_contra hbad
    have hjA : j + 1 ≤ A.card := by omega
    have hjr : j ≤ r := by omega
    have hnr : r - j ≤ (r - j) * n := by
      simpa using Nat.mul_le_mul_left (r - j) hn
    have hdiff : j + (r - j) = r := Nat.add_sub_of_le hjr
    nlinarith
  · simp [Finset.not_nonempty_iff_eq_empty.mp hA]


end S05P070
end

section
open Finset
open RoundRobinEq.CancelableBluff

namespace S05P070

section
variable {M : Type*} [DecidableEq M]

/-- Enumerate a bundle in the common ranking's order. -/
def orderedBundle (h : List M) (Y : Finset M) : List M :=
  h.filter (fun g => decide (g ∈ Y))

lemma orderedBundle_nodup {h : List M} (hh : h.Nodup) (Y : Finset M) :
    (orderedBundle h Y).Nodup := hh.filter _

lemma orderedBundle_toFinset (h : List M) (hh : IsRanking h) (Y : Finset M) :
    (orderedBundle h Y).toFinset = Y := by
  ext g
  simp [orderedBundle, hh.2 g]

lemma orderedBundle_length (h : List M) (hh : IsRanking h) (Y : Finset M) :
    (orderedBundle h Y).length = Y.card := by
  rw [← List.toFinset_card_of_nodup (orderedBundle_nodup hh.1 Y), orderedBundle_toFinset h hh Y]

lemma orderedBundle_rank_pairwise (h : List M) (hh : h.Nodup) (Y : Finset M) :
    (orderedBundle h Y).Pairwise (fun x y => h.idxOf x < h.idxOf y) := by
  have hp : h.Pairwise (fun x y => h.idxOf x < h.idxOf y) := by
    apply List.pairwise_iff_getElem.mpr
    intro a b ha hb hab
    simpa only [hh.idxOf_getElem] using hab
  exact hp.filter _

/-- Prefix capacity matches the j-th ordered deviating good to the j-th truthful
turn: it has not yet been removed at that truthful turn. -/
theorem orderedBundle_rank_ge (h : List M) (hh : IsRanking h) (Y : Finset M)
    (n i : ℕ) (hcap : ∀ j, (Y.filter (fun g => h.idxOf g < j * n + i)).card ≤ j)
    (j : ℕ) (hj : j < (orderedBundle h Y).length) :
    j * n + i ≤ h.idxOf (orderedBundle h Y)[j] := by
  classical
  let B := orderedBundle h Y
  have hjB : j < B.length := hj
  have hBn : B.Nodup := orderedBundle_nodup hh.1 Y
  have hBs : B.toFinset = Y := orderedBundle_toFinset h hh Y
  have hBr := orderedBundle_rank_pairwise h hh.1 Y
  by_contra hbad
  have hlt : h.idxOf B[j] < j * n + i := Nat.lt_of_not_ge hbad
  have hsub : (B.take (j + 1)).toFinset ⊆ Y.filter (fun g => h.idxOf g < j * n + i) := by
    intro g hg
    have hgm : g ∈ B.take (j + 1) := List.mem_toFinset.mp hg
    obtain ⟨s, hs, hsg⟩ := List.mem_take_iff_getElem.mp hgm
    have hsB : s < B.length := lt_of_lt_of_le hs (Nat.min_le_right _ _)
    have hsj : s ≤ j := by omega
    apply mem_filter.mpr
    constructor
    · rw [← hBs]
      apply List.mem_toFinset.mpr
      exact hsg ▸ List.getElem_mem hsB
    · have hle : h.idxOf B[s] ≤ h.idxOf B[j] := by
        rcases lt_or_eq_of_le hsj with hsj | rfl
        · exact Nat.le_of_lt (List.pairwise_iff_getElem.mp hBr s j hsB hj hsj)
        · rfl
      rw [hsg] at hle
      exact lt_of_le_of_lt hle hlt
  have hc := (card_le_card hsub).trans (hcap j)
  rw [List.toFinset_card_of_nodup (hBn.take : (B.take (j + 1)).Nodup), List.length_take,
    Nat.min_eq_left (Nat.succ_le_of_lt hjB)] at hc
  omega

end
end S05P070
end

section
open Finset
open RoundRobinEq.CancelableBluff

namespace S05P070

section
variable {n : ℕ} [NeZero n] {M : Type*} [Fintype M] [DecidableEq M]

/-- The concrete unilateral-deviation execution satisfies the common-ranking
prefix capacity constraint. -/
theorem deviation_prefix_card_le (h : List M) (hh : IsRanking h)
    (i : Fin n) (τ : List M) (hτ : IsRanking τ) (j : ℕ) :
    ((roundRobin (Function.update (RoundRobinEq.SubmodularBluff.bluff h) i τ) i).filter
      (fun g => h.idxOf g < j * n + i.val)).card ≤ j := by
  classical
  let σ := Function.update (RoundRobinEq.SubmodularBluff.bluff h) i τ
  have hσ : ∀ a, IsRanking (σ a) := by
    intro a
    by_cases ha : a = i
    · subst a; simpa [σ] using hτ
    · simpa [σ, Function.update_of_ne ha, RoundRobinEq.SubmodularBluff.bluff] using hh
  let p : ℕ → ℕ := fun t => ((pick σ t).map h.idxOf).getD h.length
  let A := ((range (Fintype.card M)).filter (fun t => agentAt n t = i)).filter
    (fun t => p t < j * n + i.val)
  have ha : ∀ t ∈ A, t < Fintype.card M ∧ t % n = i.val ∧ p t < j * n + i.val := by
    intro t ht
    obtain ⟨htA, htp⟩ := mem_filter.mp ht
    obtain ⟨htm, hti⟩ := mem_filter.mp htA
    exact ⟨mem_range.mp htm, congrArg Fin.val hti, htp⟩
  have hp_inj : ∀ a < Fintype.card M, ∀ b < Fintype.card M, p a = p b → a = b := by
    intro a ham b hbm heq
    obtain ⟨x, hx⟩ := pick_exists_of_lt σ hσ ham
    obtain ⟨y, hy⟩ := pick_exists_of_lt σ hσ hbm
    have hxy : x = y := (List.idxOf_inj (hh.2 x)).mp (by simpa [p, hx, hy] using heq)
    subst y
    exact pick_some_injective σ hx hy
  have hopp : ∀ t ∈ A, ∀ s < t, s % n ≠ i.val → p s ≤ p t := by
    intro t ht s hst hsi
    have htm := (ha t ht).1
    obtain ⟨x, hx⟩ := pick_exists_of_lt σ hσ htm
    obtain ⟨y, hy⟩ := pick_exists_of_lt σ hσ (lt_trans hst htm)
    have hsact : agentAt n s ≠ i := by
      intro heq
      exact hsi (congrArg Fin.val heq)
    have hsprof : σ (agentAt n s) = h := by
      simp [σ, Function.update_of_ne hsact, RoundRobinEq.SubmodularBluff.bluff]
    have hxavail : x ∉ allocBefore σ s := by
      intro hxmem
      exact (pick_not_mem_allocBefore σ hx) ((allocBefore_mono σ (Nat.le_of_lt hst)) hxmem)
    have hle := pick_idxOf_le σ hh hsprof hy hxavail
    simpa [p, hx, hy] using hle
  have hAc : A.card ≤ j := scheduled_prefix_card_le n i.val j (Fintype.card M)
    (Nat.pos_of_ne_zero (NeZero.ne n)) i.isLt p A ha hp_inj hopp
  let Y := (roundRobin σ i).filter (fun g => h.idxOf g < j * n + i.val)
  have hsub : Y.image h.idxOf ⊆ A.image p := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := mem_image.mp hx
    obtain ⟨hgY, hglt⟩ := mem_filter.mp hg
    have hex : ∃ t < Fintype.card M, agentAt n t = i ∧ pick σ t = some g := by
      simpa only [roundRobin, mem_biUnion, mem_filter, mem_range, Option.mem_toFinset,
        Option.mem_def, exists_prop, and_assoc] using hgY
    obtain ⟨t, htm, hti, htg⟩ := hex
    refine mem_image.mpr ⟨t, ?_, ?_⟩
    · simp only [A, mem_filter, mem_range]
      exact ⟨⟨htm, hti⟩, by simpa [p, htg] using hglt⟩
    · simp [p, htg]
  have hidx_inj : Function.Injective h.idxOf := by
    intro x y heq
    exact (List.idxOf_inj (hh.2 x)).mp heq
  have hYc : Y.card ≤ A.card := by
    calc
      Y.card = (Y.image h.idxOf).card := (card_image_of_injective Y hidx_inj).symm
      _ ≤ (A.image p).card := card_le_card hsub
      _ ≤ A.card := card_image_le
  exact hYc.trans hAc

/-- The ordered deviating bundle admits the exact marginal comparison required
by the submodular factor-two argument. -/
theorem deviation_marginal_le (v : Fin n → Finset M → ℝ) (h : List M)
    (hh : RoundRobinEq.SubmodularBluff.IsGreedyOrder v h)
    (i : Fin n) (τ : List M) (hτ : IsRanking τ)
    (j : ℕ)
    (hj : j < (orderedBundle h
      (roundRobin (Function.update (RoundRobinEq.SubmodularBluff.bluff h) i τ) i)).length)
    (ht : j * n + i.val < h.length) :
    marginal (v i)
      {(orderedBundle h
        (roundRobin (Function.update (RoundRobinEq.SubmodularBluff.bluff h) i τ) i))[j]}
      (RoundRobinEq.SubmodularBluff.greedyBundle n h (j * n + i.val)) ≤
    marginal (v i) {h[j * n + i.val]}
      (RoundRobinEq.SubmodularBluff.greedyBundle n h (j * n + i.val)) := by
  let Y := roundRobin (Function.update (RoundRobinEq.SubmodularBluff.bluff h) i τ) i
  let B := orderedBundle h Y
  have hrank : j * n + i.val ≤ h.idxOf B[j] :=
    orderedBundle_rank_ge h hh.1 Y n i.val
      (deviation_prefix_card_le h hh.1 i τ hτ) j hj
  have hnot : B[j] ∉ h.take (j * n + i.val) := by
    intro hmem
    have hlt := (List.mem_take_iff_idxOf_lt (hh.1.2 B[j])).mp hmem
    omega
  have hactor : agentAt n (j * n + i.val) = i := by
    apply Fin.ext
    simp [agentAt, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
  have hgreedy := hh.2 (j * n + i.val) ht B[j] hnot
  simpa only [hactor] using hgreedy

end
end S05P070
end

section
open RoundRobinEq.CancelableBluff
open scoped BigOperators

namespace S05P070

lemma actor_times_full_eq_image (n i k : ℕ) (hn : 0 < n) (hi : i < n) :
    ((Finset.range (k * n)).filter (fun t => t % n = i)) =
      (Finset.range k).image (fun r => r * n + i) := by
  ext t
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨ht, hmod⟩
    refine ⟨t / n, (Nat.div_lt_iff_lt_mul hn).2 ht, ?_⟩
    have hd := Nat.mod_add_div' t n
    omega
  · rintro ⟨r, hr, rfl⟩
    constructor
    · nlinarith
    · simp [Nat.add_mod, Nat.mod_eq_of_lt hi]

lemma actor_times_full_card (n i k : ℕ) (hn : 0 < n) (hi : i < n) :
    ((Finset.range (k * n)).filter (fun t => t % n = i)).card = k := by
  rw [actor_times_full_eq_image n i k hn hi, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    exact Nat.eq_of_mul_eq_mul_right hn (Nat.add_right_cancel hab)

lemma actor_times_before_eq_image (n i j : ℕ) (hn : 0 < n) (hi : i < n) :
    ((Finset.range (j * n + i)).filter (fun t => t % n = i)) =
      (Finset.range j).image (fun r => r * n + i) := by
  ext t
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨ht, hmod⟩
    have hd := Nat.mod_add_div' t n
    refine ⟨t / n, ?_, ?_⟩
    · nlinarith
    · omega
  · rintro ⟨r, hr, rfl⟩
    constructor
    · nlinarith
    · simp [Nat.add_mod, Nat.mod_eq_of_lt hi]

section Execution
variable {n : ℕ} [NeZero n] {M : Type*} [Fintype M] [DecidableEq M]

lemma agentAt_eq_iff (t : ℕ) (i : Fin n) : agentAt n t = i ↔ t % n = i.val := by
  exact Fin.ext_iff

lemma agentAt_ownTime (r : ℕ) (i : Fin n) : agentAt n (r * n + i.val) = i := by
  apply Fin.ext
  simp [agentAt, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]

lemma roundRobin_card (σ : Fin n → List M) (hσ : ∀ i, IsRanking (σ i))
    {k : ℕ} (hcard : Fintype.card M = k * n) (i : Fin n) :
    (roundRobin σ i).card = k := by
  unfold roundRobin
  rw [Finset.card_biUnion]
  · calc
      (∑ t ∈ (Finset.range (Fintype.card M)).filter (fun t => agentAt n t = i),
          (pick σ t).toFinset.card) =
          ∑ _t ∈ (Finset.range (Fintype.card M)).filter (fun t => agentAt n t = i), 1 := by
        apply Finset.sum_congr rfl
        intro t ht
        obtain ⟨g, hg⟩ := pick_exists_of_lt σ hσ (Finset.mem_range.mp (Finset.mem_filter.mp ht).1)
        simp [hg]
      _ = ((Finset.range (Fintype.card M)).filter (fun t => agentAt n t = i)).card := by simp
      _ = k := by
        simp_rw [hcard, agentAt_eq_iff]
        exact actor_times_full_card n i.val k (NeZero.pos n) i.isLt
  · intro s hs t ht hst
    apply Finset.disjoint_left.mpr
    intro g hgs hgt
    have hsg : pick σ s = some g := by simpa using hgs
    have htg : pick σ t = some g := by simpa using hgt
    exact hst (pick_some_injective σ hsg htg)

lemma ownTime_lt {k : ℕ} (i : Fin n) (r : Fin k) : r.val * n + i.val < k * n := by
  have hn : 0 < n := NeZero.pos n
  have hr := r.isLt
  have hi := i.isLt
  nlinarith

def ownGoods {k : ℕ} (h : List M) (hlen : h.length = k * n) (i : Fin n) : List M :=
  List.ofFn (fun r : Fin k => h[r.val * n + i.val]'(by rw [hlen]; exact ownTime_lt i r))

@[simp] lemma ownGoods_length {k : ℕ} (h : List M) (hlen : h.length = k * n) (i : Fin n) :
    (ownGoods h hlen i).length = k := by simp [ownGoods]

lemma ownGoods_getElem {k : ℕ} (h : List M) (hlen : h.length = k * n) (i : Fin n)
    (j : ℕ) (hj : j < k) :
    (ownGoods h hlen i)[j]'(by simpa using hj) =
      h[j * n + i.val]'(by rw [hlen]; exact ownTime_lt i ⟨j, hj⟩) := by
  simp [ownGoods]

lemma ownGoods_nodup {k : ℕ} (h : List M) (hlen : h.length = k * n) (i : Fin n)
    (hh : h.Nodup) : (ownGoods h hlen i).Nodup := by
  apply List.nodup_ofFn.mpr
  intro a b hab
  apply Fin.ext
  exact Nat.eq_of_mul_eq_mul_right (NeZero.pos n)
    (Nat.add_right_cancel (hh.getElem_inj_iff.mp hab))

lemma mem_ownGoods_iff {k : ℕ} (h : List M) (hlen : h.length = k * n) (i : Fin n) (g : M) :
    g ∈ ownGoods h hlen i ↔
      ∃ r : Fin k, h[r.val * n + i.val]'(by rw [hlen]; exact ownTime_lt i r) = g := by
  simp [ownGoods]

lemma ownGoods_take_eq_biUnion {k : ℕ} (h : List M) (hlen : h.length = k * n)
    (i : Fin n) (j : ℕ) (hj : j ≤ k) :
    ((ownGoods h hlen i).take j).toFinset =
      (Finset.range j).biUnion (fun r => (h[r * n + i.val]?).toFinset) := by
  ext g
  simp only [List.mem_toFinset, Finset.mem_biUnion, Finset.mem_range,
    Option.mem_toFinset]
  constructor
  · intro hg
    obtain ⟨r, hr, hrg⟩ := List.mem_take_iff_getElem.mp hg
    have hrj : r < j := lt_of_lt_of_le hr (Nat.min_le_left _ _)
    have hrk : r < k := lt_of_lt_of_le hrj hj
    refine ⟨r, hrj, ?_⟩
    rw [List.getElem?_eq_getElem (by rw [hlen]; exact ownTime_lt i ⟨r, hrk⟩)]
    simpa only [ownGoods_getElem h hlen i r hrk, Option.mem_some_iff] using hrg
  · rintro ⟨r, hrj, hrg⟩
    have hrk : r < k := lt_of_lt_of_le hrj hj
    refine List.mem_take_iff_getElem.mpr ⟨r, ?_, ?_⟩
    · simp only [ownGoods_length]
      exact lt_min hrj hrk
    · rw [ownGoods_getElem h hlen i r hrk]
      simpa only [List.getElem?_eq_getElem (by rw [hlen]; exact ownTime_lt i ⟨r, hrk⟩),
        Option.mem_some_iff] using hrg

lemma ownGoods_take_toFinset {k : ℕ} (h : List M) (hlen : h.length = k * n)
    (i : Fin n) (j : ℕ) (hj : j ≤ k) :
    ((ownGoods h hlen i).take j).toFinset =
      RoundRobinEq.SubmodularBluff.greedyBundle n h (j * n + i.val) := by
  rw [ownGoods_take_eq_biUnion h hlen i j hj]
  unfold RoundRobinEq.SubmodularBluff.greedyBundle
  rw [agentAt_ownTime]
  simp_rw [agentAt_eq_iff]
  rw [actor_times_before_eq_image n i.val j (NeZero.pos n) i.isLt,
    Finset.image_biUnion]

lemma ownGoods_toFinset {k : ℕ} (h : List M) (hh : IsRanking h)
    (hcard : Fintype.card M = k * n) (i : Fin n) :
    (ownGoods h ((ranking_length hh).trans hcard) i).toFinset =
      roundRobin (RoundRobinEq.SubmodularBluff.bluff h) i := by
  have hlen := (ranking_length hh).trans hcard
  have htake : (ownGoods h hlen i).take k = ownGoods h hlen i := by
    apply List.take_of_length_le
    simp
  rw [← htake, ownGoods_take_eq_biUnion h hlen i k le_rfl, bluff_roundRobin h hh.1 i]
  simp_rw [hcard, agentAt_eq_iff]
  rw [actor_times_full_eq_image n i.val k (NeZero.pos n) i.isLt, Finset.image_biUnion]

end Execution
end S05P070
end

section
open scoped BigOperators
open RoundRobinEq.CancelableBluff RoundRobinEq.SubmodularBluff

namespace S05P070

variable {M : Type*} [DecidableEq M] (v : Finset M → ℝ)

theorem marginal_nonneg (hv : IsValuation v) (S T : Finset M) :
    0 ≤ marginal v T S := by
  exact sub_nonneg.mpr (hv.2 S (T ∪ S) Finset.subset_union_right)

/-- Monotonicity extends diminishing marginals to goods already in the larger set. -/
theorem marginal_singleton_antitone (hv : IsValuation v) (hs : IsSubmodular v)
    {S T : Finset M} (hST : S ⊆ T) (g : M) :
    marginal v {g} T ≤ marginal v {g} S := by
  by_cases hg : g ∈ T
  · have hz : marginal v {g} T = 0 := by simp [marginal, hg]
    rw [hz]
    exact marginal_nonneg v hv S {g}
  · exact hs S T g hST hg

/-- Adding finitely many indexed goods costs no more than their initial marginals.
Repeated goods are allowed. -/
theorem value_union_image_le {I : Type*} [DecidableEq I]
    (hv : IsValuation v) (hs : IsSubmodular v) (S : Finset M)
    (g : I → M) (t : Finset I) :
    v (S ∪ t.image g) ≤ v S + ∑ i ∈ t, marginal v {g i} S := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    have hd := marginal_singleton_antitone v hv hs
      (S := S) (T := S ∪ t.image g) Finset.subset_union_left (g i)
    have heq : v (S ∪ (insert i t).image g) =
        v (S ∪ t.image g) + marginal v {g i} (S ∪ t.image g) := by
      simp only [Finset.image_insert, Finset.union_insert, marginal, Finset.singleton_union]
      ring
    rw [heq, Finset.sum_insert hi]
    linarith


/-- A list is the image of its indexed entries, including the empty list. -/
theorem list_toFinset_eq_image (A : List M) :
    A.toFinset = Finset.univ.image (fun j : Fin A.length => A[j.val]) := by
  ext g
  constructor
  · intro hg
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hg)
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
  · intro hg
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hg
    exact List.mem_toFinset.mpr (List.getElem_mem j.isLt)

/-- The marginal gains along an ordered bundle telescope. -/
theorem list_marginal_sum (A : List M) :
    (∑ j : Fin A.length, marginal v {A[j.val]} (A.take j.val).toFinset) =
      v A.toFinset - v ∅ := by
  calc
    _ = ∑ j : Fin A.length,
        (v (A.take (j.val + 1)).toFinset - v (A.take j.val).toFinset) := by
      apply Finset.sum_congr rfl
      intro j _
      have hset : (A.take (j.val + 1)).toFinset =
          {A[j.val]} ∪ (A.take j.val).toFinset := by
        rw [List.take_succ_eq_append_getElem j.isLt]
        simp only [List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
          Finset.insert_empty, Finset.union_comm]
      simp only [marginal, hset]
    _ = ∑ j ∈ Finset.range A.length,
        (v (A.take (j + 1)).toFinset - v (A.take j).toFinset) :=
      Fin.sum_univ_eq_sum_range
        (fun j => v (A.take (j + 1)).toFinset - v (A.take j).toFinset) A.length
    _ = v A.toFinset - v ∅ := by
      simpa using Finset.sum_range_sub (fun j => v (A.take j).toFinset) A.length

/-- Ordered marginal domination gives the submodular factor-two estimate. -/
theorem list_factor_two (hv : IsValuation v) (hs : IsSubmodular v)
    (A B : List M) (hLen : B.length = A.length)
    (hMarg : ∀ j (hjA : j < A.length) (hjB : j < B.length),
      marginal v {B[j]} (A.take j).toFinset ≤
        marginal v {A[j]} (A.take j).toFinset) :
    v B.toFinset ≤ 2 * v A.toFinset := by
  let b : Fin A.length → M := fun j => B[j.val]'(by omega)
  have hB : Finset.univ.image b = B.toFinset := by
    ext g
    constructor
    · intro hg
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hg
      exact List.mem_toFinset.mpr (List.getElem_mem (by omega))
    · intro hg
      obtain ⟨j, hj, hgj⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hg)
      exact Finset.mem_image.mpr ⟨⟨j, by omega⟩, Finset.mem_univ _, hgj⟩
  have hu := value_union_image_le v hv hs A.toFinset b Finset.univ
  rw [hB] at hu
  have hm : (∑ j : Fin A.length, marginal v {b j} A.toFinset) ≤
      ∑ j : Fin A.length, marginal v {A[j.val]} (A.take j.val).toFinset := by
    apply Finset.sum_le_sum
    intro j _
    have hsub : (A.take j.val).toFinset ⊆ A.toFinset := by
      intro g hg
      exact List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hg))
    exact (marginal_singleton_antitone v hv hs hsub (b j)).trans
      (hMarg j.val j.isLt (by omega))
  rw [list_marginal_sum v A, hv.1] at hm
  have hmon := hv.2 B.toFinset (A.toFinset ∪ B.toFinset) Finset.subset_union_right
  linarith

end S05P070
end

section
open RoundRobinEq.CancelableBluff

namespace S05P070

/-- The unchanged universal approximation half of the full root, proved directly
from the published recursive execution and greedy-order definitions. -/
theorem bluff_half_approx_pne {n : ℕ} [NeZero n] {M : Type*}
    [Fintype M] [DecidableEq M] (k : ℕ) (hcard : Fintype.card M = k * n)
    (v : Fin n → Finset M → ℝ)
    (hv : ∀ i, IsValuation (v i) ∧ RoundRobinEq.SubmodularBluff.IsSubmodular (v i))
    (h : List M) (hh : RoundRobinEq.SubmodularBluff.IsGreedyOrder v h) :
    IsApproxPNE (1 / 2) v (RoundRobinEq.SubmodularBluff.bluff h) := by
  refine ⟨fun _ => hh.1, ?_⟩
  intro i τ hτ
  let σ := Function.update (RoundRobinEq.SubmodularBluff.bluff h) i τ
  have hσ : ∀ a, IsRanking (σ a) := by
    intro a
    by_cases ha : a = i
    · subst a; simpa [σ] using hτ
    · simpa [σ, Function.update_of_ne ha, RoundRobinEq.SubmodularBluff.bluff] using hh.1
  let hlen : h.length = k * n := (ranking_length hh.1).trans hcard
  let A := ownGoods h hlen i
  let Y := roundRobin σ i
  let B := orderedBundle h Y
  have hAlen : A.length = k := ownGoods_length h hlen i
  have hYcard : Y.card = k := roundRobin_card σ hσ hcard i
  have hBlen : B.length = k := (orderedBundle_length h hh.1 Y).trans hYcard
  have hMarg : ∀ j (hjA : j < A.length) (hjB : j < B.length),
      marginal (v i) {B[j]} (A.take j).toFinset ≤
        marginal (v i) {A[j]} (A.take j).toFinset := by
    intro j hjA hjB
    have hjk : j < k := hAlen ▸ hjA
    have ht : j * n + i.val < h.length := by
      rw [hlen]
      exact ownTime_lt i ⟨j, hjk⟩
    have hstep := deviation_marginal_le v h hh i τ hτ j hjB ht
    rw [← ownGoods_take_toFinset h hlen i j (Nat.le_of_lt hjk),
      ← ownGoods_getElem h hlen i j hjk] at hstep
    exact hstep
  have hbound := list_factor_two (v i) (hv i).1 (hv i).2 A B
    (hBlen.trans hAlen.symm) hMarg
  have hAset : A.toFinset = roundRobin (RoundRobinEq.SubmodularBluff.bluff h) i :=
    ownGoods_toFinset h hh.1 hcard i
  have hBset : B.toFinset = Y := orderedBundle_toFinset h hh.1 Y
  rw [hAset, hBset] at hbound
  change (1 / 2 : ℝ) * v i Y ≤ v i (roundRobin (RoundRobinEq.SubmodularBluff.bluff h) i)
  linarith

end S05P070
end

section
open RoundRobinEq.CancelableBluff
open RoundRobinEq.SubmodularBluff

namespace S05P070

variable {M : Type*} [DecidableEq M]

def weightedAtom (g : M) (w : ℝ) (S : Finset M) : ℝ :=
  if g ∈ S then w else 0

lemma weightedAtom_maxitive (g : M) (w : ℝ) (hw : 0 ≤ w) (S T : Finset M) :
    weightedAtom g w (S ∪ T) = max (weightedAtom g w S) (weightedAtom g w T) := by
  by_cases hs : g ∈ S <;> by_cases ht : g ∈ T <;>
    simp [weightedAtom, hs, ht, max_eq_left hw, max_eq_right hw]

lemma maxitive_max (v w : Finset M → ℝ)
    (hv : ∀ S T, v (S ∪ T) = max (v S) (v T))
    (hw : ∀ S T, w (S ∪ T) = max (w S) (w T)) :
    ∀ S T, max (v (S ∪ T)) (w (S ∪ T)) =
      max (max (v S) (w S)) (max (v T) (w T)) := by
  intro S T
  rw [hv, hw]
  exact sup_sup_sup_comm _ _ _ _

lemma valuation_of_maxitive (v : Finset M → ℝ) (he : v ∅ = 0)
    (hu : ∀ S T, v (S ∪ T) = max (v S) (v T)) : IsValuation v := by
  refine ⟨he, ?_⟩
  intro S T hST
  have h := hu S T
  rw [Finset.union_eq_right.mpr hST] at h
  exact (le_max_left (v S) (v T)).trans_eq h.symm

lemma submodular_of_maxitive (v : Finset M → ℝ) (he : v ∅ = 0)
    (hu : ∀ S T, v (S ∪ T) = max (v S) (v T)) : IsSubmodular v := by
  intro S T g hST _
  have hmono := (valuation_of_maxitive v he hu).2 S T hST
  change v ({g} ∪ T) - v T ≤ v ({g} ∪ S) - v S
  rw [hu, hu]
  by_cases hs : v {g} ≤ v S
  · rw [max_eq_right hs, max_eq_right (hs.trans hmono)]
    simp
  · rw [max_eq_left (le_of_not_ge hs)]
    by_cases ht : v {g} ≤ v T
    · rw [max_eq_right ht]
      linarith
    · rw [max_eq_left (le_of_not_ge ht)]
      linarith

lemma valuation_submodular_of_maxitive (v : Finset M → ℝ) (he : v ∅ = 0)
    (hu : ∀ S T, v (S ∪ T) = max (v S) (v T)) :
    IsValuation v ∧ IsSubmodular v :=
  ⟨valuation_of_maxitive v he hu, submodular_of_maxitive v he hu⟩

lemma weightedAtom_valuation_submodular (g : M) (w : ℝ) (hw : 0 ≤ w) :
    IsValuation (weightedAtom g w) ∧ IsSubmodular (weightedAtom g w) :=
  valuation_submodular_of_maxitive _ (by simp [weightedAtom])
    (weightedAtom_maxitive g w hw)

lemma valuation_submodular_add (v w : Finset M → ℝ)
    (hv : IsValuation v ∧ IsSubmodular v)
    (hw : IsValuation w ∧ IsSubmodular w) :
    IsValuation (fun S => v S + w S) ∧ IsSubmodular (fun S => v S + w S) := by
  refine ⟨⟨by simp [hv.1.1, hw.1.1], ?_⟩, ?_⟩
  · intro S T hST
    exact add_le_add (hv.1.2 S T hST) (hw.1.2 S T hST)
  · intro S T g hST hg
    have h₁ := hv.2 S T g hST hg
    have h₂ := hw.2 S T g hST hg
    dsimp only [marginal] at *
    linarith

/-- The six-good sharpness family consists of modular nonnegative atoms and a
unit-demand term, so both agents have normalized monotone submodular valuations. -/
theorem tight_valuations (ε₁ ε₂ ε₃ : ℝ)
    (h₁ : ε₁ ≤ 1) (h₂ : ε₂ ≤ 1) (h₃ : ε₃ ≤ 1) :
    ∀ i : Fin 2, IsValuation (tightVal ε₁ ε₂ ε₃ i) ∧
      IsSubmodular (tightVal ε₁ ε₂ ε₃ i) := by
  have hw₁ : 0 ≤ 1 - ε₁ := by linarith
  have hw₂ : 0 ≤ 1 - ε₂ := by linarith
  have hw₃ : 0 ≤ 1 - ε₃ := by linarith
  have ha₀ := weightedAtom_valuation_submodular (0 : Fin 6) 2 (by norm_num)
  have ha₁ := weightedAtom_valuation_submodular (1 : Fin 6) 1 zero_le_one
  have ha₂ := weightedAtom_valuation_submodular (2 : Fin 6) (1 - ε₁) hw₁
  have ha₃ := weightedAtom_valuation_submodular (3 : Fin 6) (1 - ε₂) hw₂
  have ha₄ := weightedAtom_valuation_submodular (4 : Fin 6) (1 - ε₃) hw₃
  have hleft := valuation_submodular_add _ _
    (valuation_submodular_add _ _
      (valuation_submodular_add _ _ (valuation_submodular_add _ _ ha₀ ha₁) ha₂) ha₃) ha₄
  have hmax := valuation_submodular_of_maxitive
    (fun S : Finset (Fin 6) => max (weightedAtom 1 1 S)
      (max (weightedAtom 3 (1 - ε₂) S) (weightedAtom 4 (1 - ε₃) S)))
    (by simp [weightedAtom])
    (maxitive_max (weightedAtom (1 : Fin 6) 1)
      (fun S => max (weightedAtom (3 : Fin 6) (1 - ε₂) S)
        (weightedAtom (4 : Fin 6) (1 - ε₃) S))
      (weightedAtom_maxitive _ _ zero_le_one)
      (maxitive_max (weightedAtom (3 : Fin 6) (1 - ε₂))
        (weightedAtom (4 : Fin 6) (1 - ε₃))
        (weightedAtom_maxitive _ _ hw₂) (weightedAtom_maxitive _ _ hw₃)))
  have hright := valuation_submodular_add _ _ (valuation_submodular_add _ _ ha₀ ha₂) hmax
  intro i
  fin_cases i
  · convert hleft using 1 <;> rfl
  · convert hright using 1 <;> rfl

end S05P070
end

section
set_option maxHeartbeats 800000


open RoundRobinEq.SubmodularBluff
open RoundRobinEq.CancelableBluff (agentAt marginal IsRanking roundRobin)

namespace S05P070

/-- Every greedy tie-breaking starts with the same three strictly preferred
goods. The later tail need only be a permutation for the sharpness argument. -/
theorem tight_greedy_prefix (ε₁ ε₂ ε₃ : ℝ)
    (h₁ : 0 < ε₁) (h₁₂ : ε₁ < ε₂) (h₂₃ : ε₂ < ε₃) (h₃ : ε₃ < 1)
    (h : List (Fin 6)) (hg : IsGreedyOrder (tightVal ε₁ ε₂ ε₃) h) :
    ∃ t : List (Fin 6), t.Perm [3, 4, 5] ∧ h = 0 :: 1 :: 2 :: t := by
  have hw₁ : 0 ≤ 1 - ε₁ := by linarith
  have hw₂ : 0 ≤ 1 - ε₂ := by linarith
  have hw₃ : 0 ≤ 1 - ε₃ := by linarith
  cases h with
  | nil =>
    have hm := hg.1.2 (0 : Fin 6)
    simp at hm
  | cons a t =>
    have ha : a = 0 := by
      have hs := hg.2 0 (by simp) (0 : Fin 6) (by simp)
      fin_cases a <;> first
        | rfl
        | (exfalso
           norm_num [greedyBundle, agentAt, marginal, tightVal, Finset.range_add_one, Fin.ext_iff] at hs <;>
             linarith)
    subst a
    cases t with
    | nil =>
      have hm := hg.1.2 (1 : Fin 6)
      simp at hm
    | cons b t =>
      have hb₀ : b ≠ 0 := by
        intro hb
        have hn := hg.1.1
        simp [hb] at hn
      have hb : b = 1 := by
        have hs := hg.2 1 (by simp) (1 : Fin 6) (by simp)
        change marginal (tightVal ε₁ ε₂ ε₃ 1) {1} ∅ ≤
          marginal (tightVal ε₁ ε₂ ε₃ 1) {b} ∅ at hs
        fin_cases b <;> first
          | rfl
          | (exfalso
             first
             | exact hb₀ rfl
             | (norm_num [greedyBundle, agentAt, marginal, tightVal, Finset.range_add_one, Fin.ext_iff,
                 max_eq_left hw₁, max_eq_right hw₁, max_eq_left hw₂, max_eq_right hw₂,
                 max_eq_left hw₃, max_eq_right hw₃] at hs <;> linarith))
      subst b
      cases t with
      | nil =>
        have hm := hg.1.2 (2 : Fin 6)
        simp at hm
      | cons c t =>
        have hc₁ : c ≠ 1 := by
          intro hc
          have hn := hg.1.1
          simp [hc] at hn
        have hc : c = 2 := by
          have hs := hg.2 2 (by simp) (2 : Fin 6) (by simp)
          change marginal (tightVal ε₁ ε₂ ε₃ 0) {2} {0} ≤
            marginal (tightVal ε₁ ε₂ ε₃ 0) {c} {0} at hs
          fin_cases c <;> first
            | rfl
            | (exfalso
               first
               | exact hc₁ rfl
               | (norm_num [greedyBundle, agentAt, marginal, tightVal, Finset.range_add_one, Fin.ext_iff] at hs <;>
                   linarith))
        subst c
        refine ⟨t, ?_, rfl⟩
        have hn : (0 : Fin 6) ∉ t ∧ (1 : Fin 6) ∉ t ∧ (2 : Fin 6) ∉ t ∧ t.Nodup := by
          simpa using hg.1.1
        apply (List.perm_ext_iff_of_nodup hn.2.2.2 (by decide)).mpr
        intro g
        have hm := hg.1.2 g
        fin_cases g <;> simp_all

/-- Only these membership facts about the six possible tails are needed. -/
def tightRunFacts (t : List (Fin 6)) : Prop :=
  let h := 0 :: 1 :: 2 :: t
  let X := roundRobin (bluff h : Fin 2 → List (Fin 6)) 1
  let Y := roundRobin (Function.update (bluff h : Fin 2 → List (Fin 6)) 1 tightDeviation) 1
  ((1 : Fin 6) ∈ X ∧ (0 : Fin 6) ∉ X ∧ (2 : Fin 6) ∉ X) ∧
    ((2 : Fin 6) ∈ Y ∧ (3 : Fin 6) ∈ Y ∧ (0 : Fin 6) ∉ Y ∧ (1 : Fin 6) ∉ Y)

/-- A kernel-checked finite execution certificate, over just six permutations. -/
theorem tight_run_certificate :
    ∀ t ∈ ([3, 4, 5] : List (Fin 6)).permutations', tightRunFacts t := by
  unfold tightRunFacts
  decide

theorem tight_runs_of_prefix (ε₁ ε₂ ε₃ : ℝ)
    (h₂ : 0 ≤ ε₂) (h₂₃ : ε₂ ≤ ε₃) (h₃ : ε₃ ≤ 1)
    (t : List (Fin 6)) (ht : t.Perm [3, 4, 5]) :
    tightVal ε₁ ε₂ ε₃ 1 (roundRobin (bluff (0 :: 1 :: 2 :: t) : Fin 2 → List (Fin 6)) 1) = 1 ∧
    tightVal ε₁ ε₂ ε₃ 1
      (roundRobin (Function.update (bluff (0 :: 1 :: 2 :: t) : Fin 2 → List (Fin 6))
        1 tightDeviation) 1) = 2 - ε₁ - ε₂ := by
  obtain ⟨hX, hY⟩ := tight_run_certificate t (List.mem_permutations'.mpr ht)
  let X := roundRobin (bluff (0 :: 1 :: 2 :: t) : Fin 2 → List (Fin 6)) 1
  let Y := roundRobin (Function.update (bluff (0 :: 1 :: 2 :: t) : Fin 2 → List (Fin 6))
    1 tightDeviation) 1
  change (1 : Fin 6) ∈ X ∧ (0 : Fin 6) ∉ X ∧ (2 : Fin 6) ∉ X at hX
  change (2 : Fin 6) ∈ Y ∧ (3 : Fin 6) ∈ Y ∧ (0 : Fin 6) ∉ Y ∧ (1 : Fin 6) ∉ Y at hY
  have hw₂ : 0 ≤ 1 - ε₂ := by linarith
  have hw₃ : 0 ≤ 1 - ε₃ := by linarith
  have hmaxX : max (if (3 : Fin 6) ∈ X then 1 - ε₂ else 0)
      (if (4 : Fin 6) ∈ X then 1 - ε₃ else 0) ≤ 1 := by
    apply max_le
    · split_ifs <;> linarith
    · split_ifs <;> linarith
  have htailY : (if (4 : Fin 6) ∈ Y then 1 - ε₃ else 0) ≤ 1 - ε₂ := by
    split_ifs <;> linarith
  constructor
  · change tightVal ε₁ ε₂ ε₃ 1 X = 1
    simp only [tightVal, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte,
      hX.1, hX.2.1, hX.2.2, max_eq_left hmaxX]
    norm_num
  · change tightVal ε₁ ε₂ ε₃ 1 Y = 2 - ε₁ - ε₂
    simp only [tightVal, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte,
      hY.1, hY.2.1, hY.2.2.1, hY.2.2.2, max_eq_left htailY, max_eq_right hw₂]
    ring

end S05P070
end

section
open RoundRobinEq.SubmodularBluff

namespace S05P070

-- Exact accepted tight_bluff_run proof, renamed and compiled independently.
theorem tight_seed_run (ε₁ ε₂ ε₃ : ℝ) (h₁ : 0 < ε₁) (h₁₂ : ε₁ < ε₂) (h₂₃ : ε₂ < ε₃)
    (h₃ : ε₃ < 1) :
    IsGreedyOrder (tightVal ε₁ ε₂ ε₃) tightBluffOrder ∧
      RoundRobinEq.CancelableBluff.roundRobin (bluff tightBluffOrder : Fin 2 → List (Fin 6)) 0 = {0, 2, 4} ∧
      RoundRobinEq.CancelableBluff.roundRobin (bluff tightBluffOrder : Fin 2 → List (Fin 6)) 1 = {1, 3, 5} ∧
      tightVal ε₁ ε₂ ε₃ 0 {0, 2, 4} = 4 - ε₁ - ε₃ ∧
      tightVal ε₁ ε₂ ε₃ 1 {1, 3, 5} = 1 := by
  have hb : ∀ j : Fin 6, greedyBundle 2 tightBluffOrder j =
      ![(∅ : Finset (Fin 6)), ∅, {0}, {1}, {0, 2}, {1, 3}] j := by decide
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · unfold RoundRobinEq.CancelableBluff.IsRanking tightBluffOrder
    decide
  · intro j hj g hg
    have hj6 : j < 6 := by simpa [tightBluffOrder] using hj
    have hbj := hb ⟨j, hj6⟩
    rw [hbj]
    have hag : RoundRobinEq.CancelableBluff.agentAt 2 j = if j % 2 = 0 then 0 else 1 := by
      unfold RoundRobinEq.CancelableBluff.agentAt
      ext
      by_cases h : j % 2 = 0 <;> simp [h] <;> omega
    interval_cases j <;> fin_cases g <;>
      simp [tightBluffOrder, RoundRobinEq.CancelableBluff.marginal, tightVal, hag] at hg ⊢ <;>
      first | linarith | (left; linarith)
  · decide
  · decide
  · simp [tightVal]; ring
  · simp [tightVal]
    linarith

end S05P070
end

section
open RoundRobinEq.CancelableBluff
open RoundRobinEq.SubmodularBluff

namespace S05P070

/-- The sharp six-good family works for every greedy tie-breaking. -/
theorem tightness :
    ∀ ε : ℝ, 0 < ε →
      ∃ (n m k : ℕ) (_ : NeZero n) (_ : m = k * n) (v : Fin n → Finset (Fin m) → ℝ),
        (∀ i, IsValuation (v i) ∧ IsSubmodular (v i)) ∧
        (∃ h : List (Fin m), IsGreedyOrder v h) ∧
        ∀ h : List (Fin m), IsGreedyOrder v h → ¬ IsApproxPNE (1 / 2 + ε) v (bluff h) := by
  intro ε hε
  let δ : ℝ := ε / (3 + 6 * ε)
  have hden : 0 < 3 + 6 * ε := by linarith
  have hδ : 0 < δ := div_pos hε hden
  have hδsmall : δ < 1 / 6 := by
    dsimp [δ]
    apply (div_lt_iff₀ hden).mpr
    linarith
  have hδeq : δ * (3 + 6 * ε) = ε := by
    dsimp [δ]
    exact div_mul_cancel₀ ε (ne_of_gt hden)
  have h₁₂ : δ < 2 * δ := by linarith
  have h₂₃ : 2 * δ < 3 * δ := by linarith
  have h₃ : 3 * δ < 1 := by linarith
  have hgain : 1 < (1 / 2 + ε) * (2 - δ - 2 * δ) := by
    nlinarith [hδeq]
  refine ⟨2, 6, 3, inferInstance, by decide, tightVal δ (2 * δ) (3 * δ), ?_, ?_, ?_⟩
  · exact tight_valuations δ (2 * δ) (3 * δ) (by linarith) (by linarith) h₃.le
  · exact ⟨tightBluffOrder, (tight_seed_run δ (2 * δ) (3 * δ) hδ h₁₂ h₂₃ h₃).1⟩
  · intro h hg hPNE
    obtain ⟨t, ht, rfl⟩ := tight_greedy_prefix δ (2 * δ) (3 * δ) hδ h₁₂ h₂₃ h₃ h hg
    obtain ⟨hbase, hdev⟩ := tight_runs_of_prefix δ (2 * δ) (3 * δ)
      (by linarith) h₂₃.le h₃.le t ht
    have hRanking : IsRanking tightDeviation := by
      unfold IsRanking tightDeviation
      decide
    have hbound := hPNE.2 (1 : Fin 2) tightDeviation hRanking
    rw [hbase, hdev] at hbound
    exact (not_le_of_gt hgain) hbound


end S05P070
end

section
open RoundRobinEq.SubmodularBluff

theorem solution :
    (∀ {n : ℕ} [NeZero n] {M : Type} [Fintype M] [DecidableEq M] (k : ℕ),
      Fintype.card M = k * n →
      ∀ v : Fin n → Finset M → ℝ, (∀ i, RoundRobinEq.CancelableBluff.IsValuation (v i) ∧ IsSubmodular (v i)) →
      ∀ h : List M, IsGreedyOrder v h → RoundRobinEq.CancelableBluff.IsApproxPNE (1 / 2) v (bluff h)) ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ (n m k : ℕ) (_ : NeZero n) (_ : m = k * n) (v : Fin n → Finset (Fin m) → ℝ),
        (∀ i, RoundRobinEq.CancelableBluff.IsValuation (v i) ∧ IsSubmodular (v i)) ∧
        (∃ h : List (Fin m), IsGreedyOrder v h) ∧
        ∀ h : List (Fin m), IsGreedyOrder v h → ¬ RoundRobinEq.CancelableBluff.IsApproxPNE (1 / 2 + ε) v (bluff h)) := by
  constructor
  · intro n hn M hM hDec k hcard v hv h hh
    exact S05P070.bluff_half_approx_pne k hcard v hv h hh
  · exact S05P070.tightness
end

end

#print axioms solution
#check @solution

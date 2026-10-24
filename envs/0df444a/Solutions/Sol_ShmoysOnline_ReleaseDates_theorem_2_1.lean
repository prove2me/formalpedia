-- Prove2me | solution 1 for ShmoysOnline.ReleaseDates.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T14:53:35.831619+00:00
-- url     : https://prove2.me/submissions/9a968c6f-a9a0-426b-b148-91a110fcc001

import Mathlib
import Definitions.Def_ShmoysOnline_ReleaseDates_Batching

set_option autoImplicit false
open scoped NNReal
noncomputable section
open ShmoysOnline.ReleaseDates

namespace SH89

section H1

variable {D : Type}

/-- Queue order of the controller: by release time, ties by job id. -/
def h1_r (I : Instance D) (j k : ℕ) : Prop :=
  I.release j < I.release k ∨ (I.release j = I.release k ∧ j ≤ k)

theorem h1_r_antisymm (I : Instance D) {j k : ℕ} (h1 : h1_r I j k) (h2 : h1_r I k j) :
    j = k := by
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact absurd (h1.trans h2) (lt_irrefl _)
  · exact absurd h1 (by rw [h2]; exact lt_irrefl _)
  · exact absurd h2 (by rw [h1]; exact lt_irrefl _)
  · omega

theorem h1_r_trans (I : Instance D) {i j k : ℕ} (h1 : h1_r I i j) (h2 : h1_r I j k) :
    h1_r I i k := by
  unfold h1_r at *
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact Or.inl (h1.trans h2)
  · exact Or.inl (h2 ▸ h1)
  · exact Or.inl (h1 ▸ h2)
  · exact Or.inr ⟨h1.trans h2, h1'.trans h2'⟩

theorem h1_r_total (I : Instance D) (j k : ℕ) : h1_r I j k ∨ h1_r I k j := by
  unfold h1_r
  rcases lt_trichotomy (I.release j) (I.release k) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases le_total j k with h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
  · exact Or.inr (Or.inl h)

theorem h1_exists_sorted (I : Instance D) (S : Finset ℕ) :
    ∃ l : List ℕ, l.Pairwise (h1_r I) ∧ l.Nodup ∧ l.toFinset = S := by
  classical
  have : Std.Total (h1_r I) := ⟨h1_r_total I⟩
  have : IsTrans ℕ (h1_r I) := ⟨fun _ _ _ => h1_r_trans I⟩
  refine ⟨S.toList.insertionSort (h1_r I), List.pairwise_insertionSort _ _, ?_, ?_⟩
  · exact (List.perm_insertionSort _ _).nodup_iff.mpr (Finset.nodup_toList S)
  · ext j; simp [(List.perm_insertionSort (h1_r I) S.toList).mem_iff]

/-- Arrivals at time `τ`, as delivered by the event stream. -/
def h1_arr (I : Instance D) (τ : ℝ≥0) : List ℕ :=
  (I.jobs.filter (fun j => I.release j = τ)).sort (· ≤ ·)

theorem h1_mem_arr {I : Instance D} {τ : ℝ≥0} {j : ℕ} :
    j ∈ h1_arr I τ ↔ j ∈ I.jobs ∧ I.release j = τ := by
  simp [h1_arr]

theorem h1_arr_pairwise (I : Instance D) (τ : ℝ≥0) : (h1_arr I τ).Pairwise (h1_r I) := by
  have h := Finset.pairwise_sort (I.jobs.filter (fun j => I.release j = τ)) (· ≤ ·)
  refine List.Pairwise.imp_of_mem ?_ h
  intro a b ha hb hab
  have ha' := h1_mem_arr.mp ha
  have hb' := h1_mem_arr.mp hb
  exact Or.inr ⟨ha'.2.trans hb'.2.symm, hab⟩

theorem h1_arr_mergeSort (I : Instance D) (τ : ℝ≥0) :
    (h1_arr I τ).mergeSort (fun a b => decide (a ≤ b)) = h1_arr I τ := by
  apply List.mergeSort_of_pairwise
  have h := Finset.pairwise_sort (I.jobs.filter (fun j => I.release j = τ)) (· ≤ ·)
  simp [h1_arr]

theorem h1_flat (I : Instance D) (l : List ℝ≥0) (hl : l.Pairwise (· < ·)) :
    (l.flatMap (h1_arr I)).Pairwise (h1_r I) ∧ (l.flatMap (h1_arr I)).Nodup ∧
    ∀ j, j ∈ l.flatMap (h1_arr I) ↔ j ∈ I.jobs ∧ I.release j ∈ l := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.pairwise_flatMap]
    refine ⟨fun τ _ => h1_arr_pairwise I τ, hl.imp ?_⟩
    intro a b hab x hx y hy
    rw [h1_mem_arr] at hx hy
    left; rw [hx.2, hy.2]; exact hab
  · rw [List.nodup_flatMap]
    refine ⟨fun τ _ => Finset.sort_nodup _ _, hl.imp ?_⟩
    intro a b hab
    rw [Function.onFun, List.disjoint_left]
    intro x hx hy
    rw [h1_mem_arr] at hx hy
    exact (ne_of_lt hab) (hx.2.symm.trans hy.2)
  · intro j
    simp only [List.mem_flatMap, h1_mem_arr]
    constructor
    · rintro ⟨τ, hτ, hj, rfl⟩; exact ⟨hj, hτ⟩
    · rintro ⟨hj, hτ⟩; exact ⟨_, hτ, hj, rfl⟩

/-- The fold function of `controllerRun`. -/
def h1_F (r : ControllerState × List (ℝ≥0 × List ℕ) × ℕ) (e : Packet) :
    ControllerState × List (ℝ≥0 × List ℕ) × ℕ :=
  ((controllerStep r.1 e).1,
    r.2.1 ++ (if (controllerStep r.1 e).2.isEmpty then [] else [(e.time, (controllerStep r.1 e).2)]),
    r.2.2 + controllerStepCost r.1 e)

theorem h1_run (es : List Packet) :
    controllerRun es = es.foldl h1_F (⟨[], false⟩, [], 0) := rfl

/-- Packet at time `τ`, with finish-time set `Fn`. -/
def h1_pkt (I : Instance D) (Fn : Finset ℝ≥0) (τ : ℝ≥0) : Packet :=
  ⟨τ, h1_arr I τ, decide (τ ∈ Fn)⟩

theorem h1_busy (I : Instance D) (Fn : Finset ℝ≥0) :
    ∀ (l : List ℝ≥0) (w : List ℕ) (out : List (ℝ≥0 × List ℕ)) (c : ℕ),
    (∀ τ ∈ l, τ ∉ Fn) →
    ∃ c', (l.map (h1_pkt I Fn)).foldl h1_F (⟨w, true⟩, out, c) =
      (⟨w ++ l.flatMap (h1_arr I), true⟩, out, c')
  | [], w, out, c, _ => ⟨c, by simp⟩
  | τ :: l, w, out, c, h => by
    have hτ : τ ∉ Fn := h τ (by simp)
    obtain ⟨c', hc'⟩ := h1_busy I Fn l (w ++ h1_arr I τ) out
      (c + controllerStepCost ⟨w, true⟩ (h1_pkt I Fn τ)) (fun x hx => h x (by simp [hx]))
    refine ⟨c', ?_⟩
    rw [List.map_cons, List.foldl_cons]
    have : h1_F (⟨w, true⟩, out, c) (h1_pkt I Fn τ) =
        (⟨w ++ h1_arr I τ, true⟩, out, c + controllerStepCost ⟨w, true⟩ (h1_pkt I Fn τ)) := by
      simp [h1_F, controllerStep, h1_pkt, hτ, h1_arr_mergeSort]
    rw [this, hc']; simp

theorem h1_split (x : ℝ≥0) : ∀ (l : List ℝ≥0), l.Pairwise (· < ·) →
    ∃ l0 m, l = l0 ++ m ∧ (∀ τ, τ ∈ l0 ↔ τ ∈ l ∧ τ < x) ∧ (∀ τ, τ ∈ m ↔ τ ∈ l ∧ x ≤ τ)
  | [], _ => ⟨[], [], rfl, by simp, by simp⟩
  | a :: l, h => by
    rw [List.pairwise_cons] at h
    by_cases ha : a < x
    · obtain ⟨l0, m, h1, h2, h3⟩ := h1_split x l h.2
      refine ⟨a :: l0, m, by rw [h1]; rfl, ?_, ?_⟩
      · intro τ; simp only [List.mem_cons, h2]
        constructor
        · rintro (rfl | ⟨h4, h5⟩)
          · exact ⟨Or.inl rfl, ha⟩
          · exact ⟨Or.inr h4, h5⟩
        · rintro ⟨rfl | h4, h5⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨h4, h5⟩
      · intro τ; simp only [List.mem_cons, h3]
        constructor
        · rintro ⟨h4, h5⟩; exact ⟨Or.inr h4, h5⟩
        · rintro ⟨rfl | h4, h5⟩
          · exact absurd ha (not_lt.mpr h5)
          · exact ⟨h4, h5⟩
    · refine ⟨[], a :: l, rfl, ?_, ?_⟩
      · intro τ; simp only [List.not_mem_nil, false_iff, not_and, List.mem_cons]
        rintro (rfl | h4)
        · exact ha
        · exact not_lt.mpr ((not_lt.mp ha).trans (h.1 τ h4).le)
      · intro τ; simp only [List.mem_cons]
        constructor
        · rintro (rfl | h4)
          · exact ⟨Or.inl rfl, not_lt.mp ha⟩
          · exact ⟨Or.inr h4, (not_lt.mp ha).trans (h.1 τ h4).le⟩
        · exact fun h4 => h4.1

theorem h1_head {s : ℝ≥0} : ∀ (m : List ℝ≥0), m.Pairwise (· < ·) → s ∈ m →
    (∀ y ∈ m, s ≤ y) → ∃ m', m = s :: m' ∧ ∀ τ, τ ∈ m' ↔ τ ∈ m ∧ s < τ
  | [], _, h, _ => by simp at h
  | a :: m, hp, hs, hle => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp hs with h | h
    · subst h
      refine ⟨m, rfl, fun τ => ?_⟩
      constructor
      · intro hτ; exact ⟨List.mem_cons_of_mem _ hτ, hp.1 τ hτ⟩
      · rintro ⟨hτ, hτ'⟩
        rcases List.mem_cons.mp hτ with rfl | hτ
        · exact absurd hτ' (lt_irrefl _)
        · exact hτ
    · exfalso
      exact absurd (hp.1 s h) (not_lt.mpr (hle a (by simp)))

theorem h1_single {x : ℝ≥0} : ∀ (l : List ℝ≥0), l.Pairwise (· < ·) → (∀ y ∈ l, y = x) →
    l = [] ∨ l = [x]
  | [], _, _ => Or.inl rfl
  | [a], _, h => Or.inr (by simp [h a (by simp)])
  | a :: b :: l, hp, h => by
    exfalso
    have hab : a < b := (List.pairwise_cons.mp hp).1 b (by simp)
    rw [h a (by simp), h b (by simp)] at hab
    exact lt_irrefl _ hab

theorem h1_starts (P : Protocol D) (A : BaseAlgorithm D) (I : Instance D)
    (hpos : ∀ b : Batch, b.jobs ≠ [] → b.jobs.Nodup → b.jobs.toFinset ⊆ I.jobs →
      b.start < batchFinish P A I b)
    {R : Finset ℕ} {t : ℝ≥0} {bs : List Batch} (h : BatchExecution P A I R t bs) :
    R ⊆ I.jobs → ∀ b ∈ bs, t ≤ b.start ∧ b.start < batchFinish P A I b := by
  induction h with
  | done t => simp
  | next R t b rest hne hnd hw hst htail ih =>
    intro hR b' hb'
    have hsub : b.jobs.toFinset ⊆ I.jobs := by
      rw [hw]; exact (Finset.filter_subset _ _).trans hR
    have hb := hpos b hne hnd hsub
    have hts : t ≤ b.start := by
      rcases hst with h | h
      · exact h.ge
      · exact h.1.le
    rcases List.mem_cons.mp hb' with rfl | hb'
    · exact ⟨hts, hb⟩
    · have := ih (Finset.sdiff_subset.trans hR) b' hb'
      exact ⟨hts.trans (hb.le.trans this.1), this.2⟩

theorem h1_construct (P : Protocol D) (A : BaseAlgorithm D) (I : Instance D) :
    ∀ (n : ℕ) (R : Finset ℕ), R.card = n → ∀ (t : ℝ≥0),
      ∃ bs, BatchExecution P A I R t bs ∧ ∀ b ∈ bs, b.jobs.Pairwise (h1_r I) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro R hRn t
  rcases R.eq_empty_or_nonempty with rfl | hne
  · exact ⟨[], BatchExecution.done t, by simp⟩
  · obtain ⟨s, hs, hsne⟩ : ∃ s : ℝ≥0, (s = t ∨ (t < s ∧ (∀ j ∈ R, s ≤ I.release j) ∧
        ∃ j ∈ R, I.release j = s)) ∧ (R.filter (fun j => I.release j ≤ s)).Nonempty := by
      by_cases h : ∃ j ∈ R, I.release j ≤ t
      · obtain ⟨j, hj, hjt⟩ := h
        exact ⟨t, Or.inl rfl, ⟨j, Finset.mem_filter.mpr ⟨hj, hjt⟩⟩⟩
      · push Not at h
        obtain ⟨j, hj, hjmin⟩ := R.exists_min_image I.release hne
        exact ⟨I.release j, Or.inr ⟨h j hj, hjmin, j, hj, rfl⟩,
          ⟨j, Finset.mem_filter.mpr ⟨hj, le_rfl⟩⟩⟩
    obtain ⟨l, hlp, hln, hlS⟩ := h1_exists_sorted I (R.filter (fun j => I.release j ≤ s))
    let b : Batch := ⟨s, l⟩
    have hcard : (R \ l.toFinset).card < n := by
      rw [← hRn, hlS]
      exact Finset.card_lt_card (Finset.sdiff_ssubset (Finset.filter_subset _ _) hsne)
    obtain ⟨rest, hrest, hrs⟩ := ih _ hcard (R \ l.toFinset) rfl (batchFinish P A I b)
    refine ⟨b :: rest, BatchExecution.next R t b rest ?_ hln hlS hs hrest, ?_⟩
    · intro hl
      have : l.toFinset = ∅ := by simp [b] at hl; simp [hl]
      rw [hlS] at this
      rw [this] at hsne
      exact Finset.not_nonempty_empty hsne
    · intro b' hb'
      rcases List.mem_cons.mp hb' with rfl | hb'
      · exact hlp
      · exact hrs b' hb'

theorem h1_sim (P : Protocol D) (A : BaseAlgorithm D) (I : Instance D)
    (hpos : ∀ b : Batch, b.jobs ≠ [] → b.jobs.Nodup → b.jobs.toFinset ⊆ I.jobs →
      b.start < batchFinish P A I b) (Fn : Finset ℝ≥0)
    {R : Finset ℕ} {t : ℝ≥0} {bs : List Batch} (h : BatchExecution P A I R t bs) :
    ∀ (l : List ℝ≥0) (w : List ℕ) (bsy : Bool) (out : List (ℝ≥0 × List ℕ)) (c : ℕ),
    R ⊆ I.jobs →
    (∀ b ∈ bs, b.jobs.Pairwise (h1_r I)) →
    (∀ j ∈ I.jobs, j ∉ R → I.release j < t) →
    w.Pairwise (h1_r I) → w.Nodup → w.toFinset = R.filter (fun j => I.release j < t) →
    (bsy = true → t ∈ Fn) →
    (bsy = false → ∀ j ∈ R, t ≤ I.release j) →
    (∀ b ∈ bs, batchFinish P A I b ∈ Fn) →
    (∀ τ ∈ Fn, t ≤ τ → (τ = t ∧ bsy = true) ∨ ∃ b ∈ bs, batchFinish P A I b = τ) →
    l.Pairwise (· < ·) →
    (∀ τ, τ ∈ l ↔ (τ ∈ I.jobs.image I.release ∨ τ ∈ Fn) ∧ t ≤ τ) →
    ((l.map (h1_pkt I Fn)).foldl h1_F (⟨w, bsy⟩, out, c)).2.1 =
      out ++ bs.map (fun b => (b.start, b.jobs)) := by
  induction h with
  | done t =>
    intro l w bsy out c hR hsort hout hw1 hw2 hw3 hb1 hb2 hF1 hF2 hl1 hl2
    have hw : w = [] := by
      have : w.toFinset = ∅ := by rw [hw3]; simp
      simpa using this
    subst hw
    have hl : ∀ y ∈ l, y = t ∧ y ∈ Fn ∧ bsy = true := by
      intro y hy
      obtain ⟨h1, h2⟩ := (hl2 y).mp hy
      rcases h1 with h1 | h1
      · exfalso
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h1
        exact absurd h2 (not_le.mpr (hout j hj (Finset.notMem_empty j)))
      · rcases hF2 y h1 h2 with h3 | ⟨b, hb, _⟩
        · exact ⟨h3.1, h1, h3.2⟩
        · simp at hb
    rcases h1_single l hl1 (fun y hy => (hl y hy).1) with rfl | rfl
    · simp
    · obtain ⟨-, htF, hbt⟩ := hl t (by simp)
      subst hbt
      have harr : h1_arr I t = [] := List.eq_nil_iff_forall_not_mem.mpr (fun j hj => by
        rw [h1_mem_arr] at hj
        have := hout j hj.1 (Finset.notMem_empty j)
        rw [hj.2] at this
        exact lt_irrefl _ this)
      simp [h1_F, h1_pkt, controllerStep, harr, htF]
  | next R t b rest hne hnd hw hst htail ih =>
    intro l w bsy out c hR hsort hout hw1 hw2 hw3 hb1 hb2 hF1 hF2 hl1 hl2
    have hsub : b.jobs.toFinset ⊆ I.jobs := by
      rw [hw]; exact (Finset.filter_subset _ _).trans hR
    have hsf : b.start < batchFinish P A I b := hpos b hne hnd hsub
    have hts : t ≤ b.start := by
      rcases hst with h | h
      · exact h.ge
      · exact h.1.le
    have hrest := h1_starts P A I hpos htail (Finset.sdiff_subset.trans hR)
    have hmemb : ∀ j, j ∈ b.jobs ↔ j ∈ R ∧ I.release j ≤ b.start := by
      intro j; rw [← List.mem_toFinset, hw, Finset.mem_filter]
    have hR' : ∀ j, j ∈ R \ b.jobs.toFinset ↔ j ∈ R ∧ b.start < I.release j := by
      intro j; rw [Finset.mem_sdiff, List.mem_toFinset, hmemb]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, lt_of_not_ge (fun h3 => h2 ⟨h1, h3⟩)⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun h3 => absurd h3.2 (not_le.mpr h2)⟩
    have hFn : ∀ τ ∈ Fn, t ≤ τ → (τ = t ∧ bsy = true) ∨ τ = batchFinish P A I b ∨
        batchFinish P A I b < τ := by
      intro τ hτ htτ
      rcases hF2 τ hτ htτ with h1 | ⟨b', hb', rfl⟩
      · exact Or.inl h1
      · rcases List.mem_cons.mp hb' with rfl | hb'
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr ((hrest b' hb').1.trans_lt (hrest b' hb').2))
    have hsT : b.start ∈ I.jobs.image I.release ∨ b.start ∈ Fn := by
      rcases hst with h1 | ⟨h1, h2, j, hj, hjs⟩
      · cases bsy
        · obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil b.jobs hne
          obtain ⟨hjR, hjs⟩ := (hmemb j).mp hj
          have := hb2 rfl j hjR
          left
          exact Finset.mem_image.mpr ⟨j, hR hjR, le_antisymm hjs (h1 ▸ this)⟩
        · right; rw [h1]; exact hb1 rfl
      · left; exact Finset.mem_image.mpr ⟨j, hR hj, hjs⟩
    -- split the time list
    obtain ⟨l0, m, hlm, hl0mem, hmmem⟩ := h1_split b.start l hl1
    have hlpw := hl1
    rw [hlm, List.pairwise_append] at hlpw
    obtain ⟨m', hmm', hm'mem⟩ := h1_head m hlpw.2.1
      ((hmmem _).mpr ⟨(hl2 _).mpr ⟨hsT, hts⟩, le_rfl⟩) (fun y hy => ((hmmem y).mp hy).2)
    have hm'pw : m'.Pairwise (· < ·) := by
      have := hlpw.2.1; rw [hmm', List.pairwise_cons] at this; exact this.2
    obtain ⟨l1, l2, hl12, hl1mem, hl2mem⟩ := h1_split (batchFinish P A I b) m' hm'pw
    have hl12pw := hm'pw
    rw [hl12, List.pairwise_append] at hl12pw
    -- phase 0
    obtain ⟨w0, bsy0, c0, hph0, hw01, hw02, hw03, hw04⟩ : ∃ w0 bsy0 c0,
        (l0.map (h1_pkt I Fn)).foldl h1_F (⟨w, bsy⟩, out, c) = (⟨w0, bsy0⟩, out, c0) ∧
        w0.Pairwise (h1_r I) ∧ w0.Nodup ∧
        w0.toFinset = R.filter (fun j => I.release j < b.start) ∧
        (bsy0 = true → b.start ∈ Fn) := by
      rcases hst with hst | ⟨hts', hall, -⟩
      · have : l0 = [] := List.eq_nil_iff_forall_not_mem.mpr (fun τ hτ => by
          obtain ⟨h1, h2⟩ := (hl0mem τ).mp hτ
          have := ((hl2 τ).mp h1).2
          rw [hst] at h2
          exact absurd h2 (not_lt.mpr this))
        subst this
        refine ⟨w, bsy, c, rfl, hw1, hw2, ?_, ?_⟩
        · rw [hw3, hst]
        · intro h; rw [hst]; exact hb1 h
      · have hw : w = [] := by
          have : w.toFinset = ∅ := by
            rw [hw3]; apply Finset.filter_eq_empty_iff.mpr
            intro j hj; exact not_lt.mpr (hts.trans (hall j hj))
          simpa using this
        subst hw
        have hl0 : ∀ y ∈ l0, y = t ∧ bsy = true ∧ t ∈ Fn := by
          intro y hy
          obtain ⟨h1, h2⟩ := (hl0mem y).mp hy
          obtain ⟨h3, h4⟩ := (hl2 y).mp h1
          rcases h3 with h3 | h3
          · exfalso
            obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h3
            by_cases hjR : j ∈ R
            · exact absurd h2 (not_lt.mpr (hall j hjR))
            · exact absurd h4 (not_le.mpr (hout j hj hjR))
          · rcases hFn y h3 h4 with h5 | h5 | h5
            · exact ⟨h5.1, h5.2, h5.1 ▸ h3⟩
            · exact absurd h2 (not_lt.mpr (h5 ▸ hsf.le))
            · exact absurd h2 (not_lt.mpr (hsf.trans h5).le)
        have hall' : R.filter (fun j => I.release j < b.start) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro j hj; exact not_lt.mpr (hall j hj)
        rcases h1_single l0 hlpw.1 (fun y hy => (hl0 y hy).1) with h0 | h0
        · subst h0
          have hbf : bsy = false := by
            cases bsy
            · rfl
            · exfalso
              have h5 : t ∈ l := (hl2 t).mpr ⟨Or.inr (hb1 rfl), le_rfl⟩
              have h6 : t ∈ ([] : List ℝ≥0) := (hl0mem t).mpr ⟨h5, hts'⟩
              simp at h6
          subst hbf
          refine ⟨[], false, c, rfl, List.Pairwise.nil, List.nodup_nil, ?_, by simp⟩
          rw [hall']; rfl
        · subst h0
          obtain ⟨_, hbt, htF⟩ := hl0 t (by simp)
          subst hbt
          have harr : h1_arr I t = [] := List.eq_nil_iff_forall_not_mem.mpr (fun j hj => by
            rw [h1_mem_arr] at hj
            by_cases hjR : j ∈ R
            · have := hall j hjR; rw [hj.2] at this; exact absurd hts' (not_lt.mpr this)
            · have := hout j hj.1 hjR; rw [hj.2] at this; exact lt_irrefl _ this)
          refine ⟨[], false, c + controllerStepCost ⟨[], true⟩ (h1_pkt I Fn t), ?_, List.Pairwise.nil, List.nodup_nil, ?_, by simp⟩
          · simp [h1_F, h1_pkt, controllerStep, harr, htF]
          · rw [hall']; rfl
    -- dispatch
    have harr_s : ∀ j, j ∈ h1_arr I b.start ↔ j ∈ R ∧ I.release j = b.start := by
      intro j; rw [h1_mem_arr]; constructor
      · rintro ⟨hj, hjs⟩
        refine ⟨?_, hjs⟩
        by_contra hjR
        have := hout j hj hjR
        rw [hjs] at this
        exact absurd (this.trans_le hts) (lt_irrefl _)
      · rintro ⟨hj, hjs⟩; exact ⟨hR hj, hjs⟩
    have hdisp : w0 ++ h1_arr I b.start = b.jobs := by
      apply List.Perm.eq_of_pairwise (le := h1_r I) (fun _ _ _ _ h1 h2 => h1_r_antisymm I h1 h2)
      · rw [List.pairwise_append]
        refine ⟨hw01, h1_arr_pairwise I _, ?_⟩
        intro x hx y hy
        have hx' : x ∈ w0.toFinset := List.mem_toFinset.mpr hx
        rw [hw03, Finset.mem_filter] at hx'
        rw [harr_s] at hy
        left; rw [hy.2]; exact hx'.2
      · exact hsort b (by simp)
      · apply List.perm_of_nodup_nodup_toFinset_eq
        · rw [List.nodup_append]
          refine ⟨hw02, Finset.sort_nodup _ _, ?_⟩
          intro x hx y hy hxy
          subst hxy
          have hx' : x ∈ w0.toFinset := List.mem_toFinset.mpr hx
          rw [hw03, Finset.mem_filter] at hx'
          rw [harr_s] at hy
          rw [hy.2] at hx'
          exact lt_irrefl _ hx'.2
        · exact hnd
        · ext j
          have hx : j ∈ w0 ↔ j ∈ R ∧ I.release j < b.start := by
            rw [← List.mem_toFinset, hw03, Finset.mem_filter]
          rw [List.toFinset_append, Finset.mem_union, List.mem_toFinset, List.mem_toFinset,
            List.mem_toFinset, hmemb, hx, harr_s]
          constructor
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · exact ⟨h1, h2.le⟩
            · exact ⟨h1, h2.le⟩
          · rintro ⟨h1, h2⟩
            rcases h2.lt_or_eq with h2 | h2
            · exact Or.inl ⟨h1, h2⟩
            · exact Or.inr ⟨h1, h2⟩
    have hcond : (bsy0 && !decide (b.start ∈ Fn)) = false := by
      cases bsy0
      · rfl
      · simp [hw04 rfl]
    have hne' : b.jobs.isEmpty = false := by
      cases hb : b.jobs with
      | nil => exact absurd hb hne
      | cons _ _ => rfl
    have hdstep : ∃ c1, h1_F (⟨w0, bsy0⟩, out, c0) (h1_pkt I Fn b.start) =
        (⟨[], true⟩, out ++ [(b.start, b.jobs)], c1) := by
      refine ⟨c0 + controllerStepCost ⟨w0, bsy0⟩ (h1_pkt I Fn b.start), ?_⟩
      simp only [h1_F, controllerStep, h1_pkt, h1_arr_mergeSort, hdisp, hcond, hne']
      simp [hne]
    obtain ⟨c1, hc1⟩ := hdstep
    -- busy phase
    have hl1nF : ∀ τ ∈ l1, τ ∉ Fn := by
      intro τ hτ hτF
      obtain ⟨h1', h3⟩ := (hl1mem τ).mp hτ
      obtain ⟨h1, h2⟩ := (hm'mem τ).mp h1'
      obtain ⟨h4, h5⟩ := (hmmem τ).mp h1
      obtain ⟨-, h6⟩ := (hl2 τ).mp h4
      rcases hFn τ hτF h6 with h7 | h7 | h7
      · rw [h7.1] at h2; exact absurd (hts.trans_lt h2) (lt_irrefl _)
      · exact absurd h7 (ne_of_lt h3)
      · exact absurd h7 (not_lt.mpr h3.le)
    obtain ⟨c2, hc2⟩ := h1_busy I Fn l1 [] (out ++ [(b.start, b.jobs)]) c1 hl1nF
    obtain ⟨hW1, hW2, hW3⟩ := h1_flat I l1 hl12pw.1
    have hWset : (l1.flatMap (h1_arr I)).toFinset = (R \ b.jobs.toFinset).filter
        (fun j => I.release j < batchFinish P A I b) := by
      ext j
      rw [List.mem_toFinset, hW3, Finset.mem_filter, hR', hl1mem, hm'mem, hmmem, hl2]
      constructor
      · rintro ⟨hj, ⟨⟨⟨-, h2⟩, -⟩, h3⟩, h4⟩
        refine ⟨⟨?_, h3⟩, h4⟩
        by_contra hjR
        exact absurd (hout j hj hjR) (not_lt.mpr h2)
      · rintro ⟨⟨hj, h3⟩, h4⟩
        exact ⟨hR hj, ⟨⟨⟨Or.inl (Finset.mem_image_of_mem _ (hR hj)), hts.trans h3.le⟩,
          h3.le⟩, h3⟩, h4⟩
    -- the rest
    have hIH := ih l2 (l1.flatMap (h1_arr I)) true (out ++ [(b.start, b.jobs)]) c2
      (Finset.sdiff_subset.trans hR) (fun b' hb' => hsort b' (List.mem_cons_of_mem _ hb'))
      (by
        intro j hj hjR
        by_cases hjR0 : j ∈ R
        · have : ¬ b.start < I.release j := fun h => hjR ((hR' j).mpr ⟨hjR0, h⟩)
          exact (not_lt.mp this).trans_lt hsf
        · exact (hout j hj hjR0).trans_le (hts.trans hsf.le))
      hW1 hW2 hWset (fun _ => hF1 b (by simp)) (fun h => by simp at h)
      (fun b' hb' => hF1 b' (List.mem_cons_of_mem _ hb'))
      (by
        intro τ hτ hfτ
        rcases hF2 τ hτ (hts.trans (hsf.le.trans hfτ)) with h1 | ⟨b', hb', h2⟩
        · exfalso; rw [h1.1] at hfτ; exact absurd (hts.trans_lt hsf) (not_lt.mpr hfτ)
        · rcases List.mem_cons.mp hb' with rfl | hb'
          · exact Or.inl ⟨h2.symm, rfl⟩
          · exact Or.inr ⟨b', hb', h2⟩)
      hl12pw.2.1
      (by
        intro τ
        rw [hl2mem, hm'mem, hmmem, hl2]
        constructor
        · rintro ⟨⟨⟨⟨h1, -⟩, -⟩, -⟩, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          have h3 : b.start < τ := hsf.trans_le h2
          exact ⟨⟨⟨⟨h1, hts.trans h3.le⟩, h3.le⟩, h3⟩, h2⟩)
    rw [hlm, hmm', hl12, List.map_append, List.foldl_append, hph0, List.map_cons,
      List.foldl_cons, hc1, List.map_append, List.foldl_append, hc2, List.nil_append, hIH]
    simp

end H1

/-- (H1) existence of the batch execution and the event stream, and agreement of the
controller output with the batches. -/
theorem exists_exec {D : Type} (P : Protocol D) (A : BaseAlgorithm D) (I : Instance D)
    (hpos : ∀ b : Batch, b.jobs ≠ [] → b.jobs.Nodup → b.jobs.toFinset ⊆ I.jobs →
      b.start < batchFinish P A I b) :
    ∃ (bs : List Batch) (es : List Packet),
      BatchExecution P A I I.jobs 0 bs ∧ EventsFor P A I bs es ∧
      (controllerRun es).2.1 = bs.map (fun b => (b.start, b.jobs)) := by
  obtain ⟨bs, hbs, hsort⟩ := h1_construct P A I _ I.jobs rfl 0
  let Fn : Finset ℝ≥0 := (bs.map (batchFinish P A I)).toFinset
  let L : List ℝ≥0 := (I.jobs.image I.release ∪ Fn).sort (· ≤ ·)
  have hL : L.Pairwise (· < ·) :=
    ((Finset.pairwise_sort _ _).and (Finset.sort_nodup _ _)).imp
      (fun h => lt_of_le_of_ne h.1 h.2)
  have hLmem : ∀ τ, τ ∈ L ↔ τ ∈ I.jobs.image I.release ∨ τ ∈ Fn := by
    intro τ; simp only [L, Finset.mem_sort, Finset.mem_union]
  have hFn : ∀ τ, τ ∈ Fn ↔ ∃ b ∈ bs, batchFinish P A I b = τ := by
    intro τ; simp [Fn]
  have hflat : (L.map (h1_pkt I Fn)).flatMap Packet.arrivals = L.flatMap (h1_arr I) := by
    simp [List.flatMap_map, h1_pkt]
  obtain ⟨-, hN, hM⟩ := h1_flat I L hL
  refine ⟨bs, L.map (h1_pkt I Fn), hbs, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact List.pairwise_map.mpr hL
    · rw [hflat]; exact hN
    · ext j
      rw [hflat, List.mem_toFinset, hM, hLmem]
      constructor
      · exact fun h => h.1
      · intro hj; exact ⟨hj, Or.inl (Finset.mem_image_of_mem _ hj)⟩
    · intro e he
      obtain ⟨τ, -, rfl⟩ := List.mem_map.mp he
      rfl
    · intro e he j hj
      obtain ⟨τ, -, rfl⟩ := List.mem_map.mp he
      exact (h1_mem_arr.mp hj).2
    · intro e he
      obtain ⟨τ, -, rfl⟩ := List.mem_map.mp he
      simp only [h1_pkt, decide_eq_true_iff]
      exact hFn τ
    · intro b hb
      refine ⟨h1_pkt I Fn (batchFinish P A I b), List.mem_map.mpr ⟨_, ?_, rfl⟩, rfl, ?_⟩
      · exact (hLmem _).mpr (Or.inr ((hFn _).mpr ⟨b, hb, rfl⟩))
      · simp only [h1_pkt, decide_eq_true_iff]
        exact (hFn _).mpr ⟨b, hb, rfl⟩
    · intro e he
      obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp he
      rcases (hLmem τ).mp hτ with h | h
      · left
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
        exact List.ne_nil_of_mem (h1_mem_arr.mpr ⟨hj, rfl⟩)
      · right
        simpa [h1_pkt] using h
  · rw [h1_run]
    have := h1_sim P A I hpos Fn hbs L [] false [] 0 subset_rfl hsort
      (fun j hj hj' => absurd hj hj') List.Pairwise.nil List.nodup_nil (by simp)
      (fun h => by simp at h) (fun _ _ _ => zero_le)
      (fun b hb => (hFn _).mpr ⟨b, hb, rfl⟩)
      (fun τ hτ _ => Or.inr ((hFn τ).mp hτ)) hL
      (fun τ => by rw [hLmem]; simp)
    simpa using this


theorem h2_causal_gen : ∀ (s : ControllerState) (h k : List Packet) (n : ℕ),
    h.take n = k.take n →
    (controllerActionsFrom s h).take n = (controllerActionsFrom s k).take n := by
  intro s h
  induction h generalizing s with
  | nil =>
    intro k n hk
    cases n with
    | zero => simp
    | succ n =>
      cases k with
      | nil => rfl
      | cons b k => simp at hk
  | cons a h ih =>
    intro k n hk
    cases n with
    | zero => simp
    | succ n =>
      cases k with
      | nil => simp at hk
      | cons b k =>
        simp only [List.take_succ_cons, List.cons.injEq] at hk
        obtain ⟨rfl, hk⟩ := hk
        simp only [controllerActionsFrom, List.take_succ_cons]
        rw [ih _ k n hk]

theorem causal : ControllerCausal := by
  intro h k n hk
  exact h2_causal_gen _ h k n hk

theorem exec_struct {D : Type} {P : Protocol D} {A : BaseAlgorithm D} {I : Instance D}
    {R : Finset ℕ} {t : ℝ≥0} {bs : List Batch} (h : BatchExecution P A I R t bs) :
    bs.length ≤ R.card ∧ (bs.map (fun b => b.jobs.toFinset)).Pairwise Disjoint ∧
      (bs.flatMap Batch.jobs).toFinset = R ∧
      ∀ b ∈ bs, b.jobs ≠ [] ∧ b.jobs.Nodup ∧ b.jobs.toFinset ⊆ R := by
  induction h with
  | done t => simp
  | next remaining t b rest hne hnd hw _ _ ih =>
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
    have hsub : b.jobs.toFinset ⊆ remaining := by
      rw [hw]; exact Finset.filter_subset _ _
    have hnem : b.jobs.toFinset.Nonempty := by
      rw [List.toFinset_nonempty_iff]; exact hne
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := Finset.card_lt_card (Finset.sdiff_ssubset hsub hnem)
      simp only [List.length_cons]; omega
    · simp only [List.map_cons, List.pairwise_cons, List.mem_map]
      refine ⟨?_, ih2⟩
      rintro _ ⟨b', hb', rfl⟩
      have := (ih4 b' hb').2.2
      exact Finset.disjoint_of_subset_right this Finset.disjoint_sdiff
    · simp only [List.flatMap_cons, List.toFinset_append, ih3]
      exact Finset.union_sdiff_of_subset hsub
    · intro b' hb'
      rcases List.mem_cons.1 hb' with rfl | hb'
      · exact ⟨hne, hnd, hsub⟩
      · obtain ⟨a1, a2, a3⟩ := ih4 b' hb'
        exact ⟨a1, a2, a3.trans Finset.sdiff_subset⟩

theorem h2_step_len (s : ControllerState) (e : Packet) :
    (controllerStep s e).1.waiting.length ≤ s.waiting.length + e.arrivals.length ∧
    (controllerStep s e).2.length ≤ s.waiting.length + e.arrivals.length := by
  unfold controllerStep
  simp only [List.isEmpty_iff]
  split_ifs <;> simp [List.length_mergeSort]

theorem h2_fold_bound (es : List Packet) : ∀ (s : ControllerState)
    (l : List (ℝ≥0 × List ℕ)) (acc : ℕ),
    (es.foldl (fun r e =>
      let z := controllerStep r.1 e
      (z.1, r.2.1 ++ (if z.2.isEmpty then [] else [(e.time, z.2)]),
        r.2.2 + controllerStepCost r.1 e)) (s, l, acc)).2.2 ≤
      acc + es.length * (3 + 2 * (s.waiting.length +
        (es.map (fun e => e.arrivals.length)).sum)) +
        (es.map (fun e => e.arrivals.length)).sum +
        (es.map (fun e => e.arrivals.length)).sum ^ 2 := by
  induction es with
  | nil => intro s l acc; simp
  | cons e es ih =>
    intro s l acc
    rw [List.foldl_cons]
    refine (ih _ _ _).trans ?_
    obtain ⟨h1, h2⟩ := h2_step_len s e
    simp only [List.map_cons, List.sum_cons, List.length_cons, controllerStepCost]
    set A := (es.map (fun e => e.arrivals.length)).sum
    set a := e.arrivals.length
    set w := s.waiting.length
    set w' := (controllerStep s e).1.waiting.length
    set d := (controllerStep s e).2.length
    set L := es.length
    have h3 : L * (3 + 2 * (w' + A)) ≤ L * (3 + 2 * (w + (a + A))) :=
      Nat.mul_le_mul_left _ (by omega)
    nlinarith

theorem h2_nonempty_count (es : List Packet) :
    (es.filter (fun e => !e.arrivals.isEmpty)).length ≤
      (es.map (fun e => e.arrivals.length)).sum := by
  induction es with
  | nil => simp
  | cons e es ih =>
    rw [List.filter_cons]
    split_ifs with h
    · simp only [List.length_cons, List.map_cons, List.sum_cons]
      have : e.arrivals ≠ [] := by simpa using h
      have := List.length_pos_of_ne_nil this
      omega
    · simp only [List.map_cons, List.sum_cons]; omega


theorem h2_sort_sum (s : Finset ℕ) (f : ℕ → ℕ) : ((s.sort (· ≤ ·)).map f).sum = s.sum f := by
  rw [← List.sum_toFinset f (Finset.sort_nodup _ _), Finset.sort_toFinset]

theorem h2_len_le (es : List Packet) (bs : List Batch) (F : Batch → ℝ≥0)
    (hp : es.Pairwise (fun a b => a.time < b.time))
    (hf : ∀ e ∈ es, e.finished = true → ∃ b ∈ bs, F b = e.time)
    (hne : ∀ e ∈ es, e.arrivals ≠ [] ∨ e.finished = true) :
    es.length ≤ (es.map (fun e => e.arrivals.length)).sum + bs.length := by
  have hsplit := List.length_eq_length_filter_add (l := es) (fun e => !e.arrivals.isEmpty)
  have h1 := h2_nonempty_count es
  set G := es.filter (fun e => !!e.arrivals.isEmpty) with hG
  have hGp : G.Pairwise (fun a b => a.time < b.time) := hp.filter _
  have hnd : (G.map Packet.time).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact hGp.imp (fun h => ne_of_lt h)
  have hsub : (G.map Packet.time).toFinset ⊆ (bs.map F).toFinset := by
    intro x hx
    simp only [List.mem_toFinset, List.mem_map, List.mem_filter, hG] at hx ⊢
    obtain ⟨e, ⟨he, hemp⟩, rfl⟩ := hx
    have hfin : e.finished = true := by
      rcases hne e he with h | h
      · simp at hemp; exact absurd hemp h
      · exact h
    obtain ⟨b, hb, hbF⟩ := hf e he hfin
    exact ⟨b, hb, hbF⟩
  have h2 : G.length ≤ bs.length := by
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd, List.length_map] at this
    exact this.trans ((List.toFinset_card_le _).trans (by simp))
  omega

theorem h2_batch_input {D : Type} (P : Protocol D) (I : Instance D) (l : List ℕ)
    (hnd : l.Nodup) (hs : l.toFinset ⊆ I.jobs) :
    inputSize P (l.map (fun j => (j, I.data j))) ≤ inputSize P (batchData I I.jobs) := by
  unfold inputSize batchData
  simp only [List.map_map]
  have e1 := List.sum_toFinset (fun j => 2 + (P.encode (I.data j)).length) hnd
  have e2 := h2_sort_sum I.jobs (fun j => 2 + (P.encode (I.data j)).length)
  have hle := Finset.sum_le_sum_of_subset (f := fun j => 2 + (P.encode (I.data j)).length) hs
  simp only [Function.comp_def] at e1 e2 ⊢
  omega

theorem h2_input_ge {D : Type} (P : Protocol D) (I : Instance D) :
    1 + 2 * I.jobs.card ≤ inputSize P (batchData I I.jobs) := by
  unfold inputSize batchData
  simp only [List.map_map]
  have e2 := h2_sort_sum I.jobs (fun j => 2 + (P.encode (I.data j)).length)
  have : ∑ j ∈ I.jobs, 2 ≤ ∑ j ∈ I.jobs, (2 + (P.encode (I.data j)).length) :=
    Finset.sum_le_sum (fun j _ => by omega)
  simp only [Finset.sum_const, smul_eq_mul, Function.comp_def] at this e2 ⊢
  omega

theorem cost_bound {D : Type} [Inhabited D] (E : Environment D) (P : Protocol D)
    (A : BaseAlgorithm D) (ρ : ℝ≥0) (c d : ℕ) (hA : Eligible E P A ρ c d)
    (I : Instance D) (hI : Valid E I) (bs : List Batch) (es : List Packet)
    (hb : BatchExecution P A I I.jobs 0 bs) (he : EventsFor P A I bs es) :
    computationCost P A I bs es ≤
      I.jobs.card * c * (releasedInputSize P I + 1) ^ d +
        10 * (releasedInputSize P I + 1) ^ 2 := by
  obtain ⟨hlen, -, -, hbs⟩ := exec_struct hb
  obtain ⟨hp, hnd, hfs, -, -, hfin, -, hne⟩ := he
  set n := I.jobs.card with hn
  set N := releasedInputSize P I with hN
  have hNge : 3 * n + 1 ≤ N := by
    have := h2_input_ge P I
    simp only [hN, releasedInputSize]; omega
  -- arrivals sum
  have hsum : (es.map (fun e => e.arrivals.length)).sum = n := by
    have h1 : (es.flatMap Packet.arrivals).length = n := by
      rw [← List.toFinset_card_of_nodup hnd, hfs]
    rw [List.length_flatMap] at h1
    simpa [Function.comp_def] using h1
  have hL : es.length ≤ 2 * n := by
    have := h2_len_le es bs (batchFinish P A I) hp
      (fun e he' hf => (hfin e he').1 hf) hne
    omega
  -- controller part
  have hctrl : (controllerRun es).2.2 ≤ 5 * n ^ 2 + 7 * n := by
    have := h2_fold_bound es ⟨[], false⟩ [] 0
    simp only [List.length_nil, hsum] at this
    unfold controllerRun
    refine this.trans ?_
    have : es.length * (3 + 2 * (0 + n)) ≤ 2 * n * (3 + 2 * (0 + n)) :=
      Nat.mul_le_mul_right _ hL
    nlinarith
  -- batch part
  have hbatch : ∀ b ∈ bs,
      (baseState P A (b.jobs.map (fun j => (j, I.data j)))).cost ≤ c * (N + 1) ^ d := by
    intro b hb'
    obtain ⟨hbne, hbnd, hbsub⟩ := hbs b hb'
    have hv : ValidBatch E (b.jobs.map (fun j => (j, I.data j))) := by
      refine ⟨?_, ?_⟩
      · simpa [List.map_map, Function.comp_def] using hbnd
      · intro x hx
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
        exact hI j (hbsub (List.mem_toFinset.2 hj))
    have hB : b.jobs.map (fun j => (j, I.data j)) ≠ [] := by simpa using hbne
    have hc := (hA.2 _ hv hB).2.2.1
    refine hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
    have := h2_batch_input P I b.jobs hbnd hbsub
    simp only [hN, releasedInputSize]; omega
  have hbsum : (bs.map (fun b =>
      (baseState P A (b.jobs.map (fun j => (j, I.data j)))).cost)).sum ≤
      n * c * (N + 1) ^ d := by
    refine (List.sum_le_card_nsmul _ (c * (N + 1) ^ d) ?_).trans ?_
    · intro x hx
      obtain ⟨b, hb', rfl⟩ := List.mem_map.1 hx
      exact hbatch b hb'
    · simp only [List.length_map, smul_eq_mul]
      rw [mul_assoc]
      exact Nat.mul_le_mul_right _ hlen
  unfold computationCost
  have : 5 * n ^ 2 + 7 * n ≤ 10 * (N + 1) ^ 2 := by nlinarith
  omega


theorem h3_find {D : Type} (l : List ℕ) (f : ℕ → D) (j : ℕ) (hj : j ∈ l) :
    ((l.map (fun i => (i, f i))).find? (fun x => x.1 == j)).map Prod.snd = some (f j) := by
  induction l with
  | nil => simp at hj
  | cons a l ih =>
    by_cases ha : a = j
    · subst ha; simp
    · have : j ∈ l := by
        rcases List.mem_cons.1 hj with h | h
        · exact absurd h.symm ha
        · exact h
      rw [List.map_cons, List.find?_cons_of_neg (by simp [ha])]; exact ih this

theorem h3_span {p : Profile} {a : Slice} (ha : a ∈ p) : a.hi ≤ span p := by
  induction p with
  | nil => simp at ha
  | cons x p ih =>
    simp only [span, List.map_cons, List.foldr_cons] at *
    rcases List.mem_cons.1 ha with h | h
    · subst h; exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem h3_feas_congr {D : Type} (E : Environment D) (I1 I2 : Instance D) (s : Schedule)
    (hj : I1.jobs = I2.jobs) (hd : ∀ j ∈ I1.jobs, I1.data j = I2.data j)
    (hr : ∀ j ∈ I1.jobs, I1.release j = I2.release j) :
    Feasible E I1 s → Feasible E I2 s := by
  rintro ⟨h1, h2⟩
  refine ⟨fun j hj2 => ?_, fun j hj2 k hk2 => ?_⟩
  · have hj1 : j ∈ I1.jobs := hj ▸ hj2
    rw [← hd j hj1, ← hr j hj1]; exact h1 j hj1
  · exact h2 j (hj ▸ hj2) k (hj ▸ hk2)

theorem h3_batch {D : Type} [Inhabited D] (E : Environment D) (P : Protocol D)
    (A : BaseAlgorithm D) (ρ : ℝ≥0) (c d : ℕ) (hA : Eligible E P A ρ c d)
    (I : Instance D) (hI : Valid E I) (b : Batch) (hne : b.jobs ≠ []) (hnd : b.jobs.Nodup)
    (hsub : b.jobs.toFinset ⊆ I.jobs) :
    Approx E (zeroInstance I b.jobs.toFinset) ρ (batchSchedule P A I b) := by
  set B := b.jobs.map (fun j => (j, I.data j)) with hBdef
  have hv : ValidBatch E B := by
    refine ⟨?_, ?_⟩
    · simp [B, List.map_map, Function.comp_def]; exact hnd
    · intro x hx
      simp only [B, List.mem_map] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      exact hI a (hsub (List.mem_toFinset.2 ha))
  have hB : B ≠ [] := by simp [B, hne]
  obtain ⟨-, -, -, -, ⟨hf, hopt⟩⟩ := hA.2 B hv hB
  have hjobs : (batchInstance B).jobs = b.jobs.toFinset := by
    simp [batchInstance, B, List.map_map, Function.comp_def]
  have hdata : ∀ j ∈ (batchInstance B).jobs, (batchInstance B).data j = (zeroInstance I b.jobs.toFinset).data j := by
    intro j hj
    rw [hjobs, List.mem_toFinset] at hj
    simp only [batchInstance, zeroInstance]
    rw [h3_find b.jobs I.data j hj]; rfl
  have hrel : ∀ j ∈ (batchInstance B).jobs, (batchInstance B).release j = (zeroInstance I b.jobs.toFinset).release j := fun _ _ => rfl
  refine ⟨h3_feas_congr E _ _ _ hjobs hdata hrel hf, fun u hu => ?_⟩
  have := hopt u (h3_feas_congr E _ _ _ hjobs.symm (fun j hj => (hdata j (hjobs ▸ hj)).symm)
    (fun _ _ => rfl) hu)
  rw [hjobs] at this
  exact this

theorem h3_compl_le {J : Finset ℕ} {s : Schedule} {j : ℕ} (hj : j ∈ J) :
    completion s j ≤ makespan J s := Finset.le_sup (f := completion s) hj

theorem h3_ratio {D : Type} (E : Environment D) (I : Instance D) (ρ : ℝ≥0) (hρ : 1 ≤ ρ)
    (J : Finset ℕ) (hJ : J ⊆ I.jobs) (hne : J.Nonempty) (s : Schedule)
    (hs : Approx E (zeroInstance I J) ρ s) (u : Schedule) (hu : Feasible E I u)
    (σ : ℝ≥0) (hσ : ∀ j ∈ J, σ ≤ I.release j) :
    σ + makespan J s ≤ ρ * makespan I.jobs u := by
  set M := makespan I.jobs u with hM
  have hσs : ∀ j ∈ J, σ ≤ (u j).start := fun j hj => (hσ j hj).trans (hu.1 j (hJ hj)).1
  have hu' : Feasible E (zeroInstance I J) (untranslate σ u) := by
    refine ⟨fun j hj => ⟨zero_le, (hu.1 j (hJ hj)).2.1, (hu.1 j (hJ hj)).2.2⟩,
      fun j hj k hk hjk a ha b hb hd => ?_⟩
    rcases hu.2 j (hJ hj) k (hJ hk) hjk a ha b hb hd with h | h
    · left
      show (u j).start - σ + a.hi ≤ (u k).start - σ + b.lo
      rw [tsub_add_eq_add_tsub (hσs j hj), tsub_add_eq_add_tsub (hσs k hk)]
      exact tsub_le_tsub_right h σ
    · right
      show (u k).start - σ + b.hi ≤ (u j).start - σ + a.lo
      rw [tsub_add_eq_add_tsub (hσs j hj), tsub_add_eq_add_tsub (hσs k hk)]
      exact tsub_le_tsub_right h σ
  have h1 := hs.2 _ hu'
  have h2 : makespan J (untranslate σ u) ≤ M - σ := by
    refine Finset.sup_le fun j hj => ?_
    show (u j).start - σ + span (u j).profile ≤ M - σ
    rw [tsub_add_eq_add_tsub (hσs j hj)]
    exact tsub_le_tsub_right (h3_compl_le (s := u) (hJ hj)) σ
  obtain ⟨j0, hj0⟩ := hne
  have hσM : σ ≤ M := (hσs j0 hj0).trans
    ((le_self_add : (u j0).start ≤ completion u j0).trans (h3_compl_le (hJ hj0)))
  calc σ + makespan J s ≤ ρ * σ + ρ * (M - σ) := by
        gcongr
        · exact le_mul_of_one_le_left (zero_le) hρ
        · exact h1.trans (mul_le_mul_right h2 ρ)
    _ = ρ * M := by rw [← mul_add, add_tsub_cancel_of_le hσM]

theorem h3_asJ {D : Type} (P : Protocol D) (A : BaseAlgorithm D) (I : Instance D)
    (b : Batch) (rest : List Batch) (j : ℕ) (hj : j ∈ b.jobs.toFinset) :
    assembled P A I (b :: rest) j = translate b.start (batchSchedule P A I b) j := by
  simp [assembled, join, hj]

theorem h3_asN {D : Type} (P : Protocol D) (A : BaseAlgorithm D) (I : Instance D)
    (b : Batch) (rest : List Batch) (j : ℕ) (hj : j ∉ b.jobs.toFinset) :
    assembled P A I (b :: rest) j = assembled P A I rest j := by
  simp only [assembled, join, hj, if_false]

theorem h3_end {D : Type} (P : Protocol D) (A : BaseAlgorithm D) (I : Instance D)
    (b : Batch) (j : ℕ) (hj : j ∈ b.jobs.toFinset) (a : Slice)
    (ha : a ∈ (batchSchedule P A I b j).profile) :
    b.start + (batchSchedule P A I b j).start + a.hi ≤ batchFinish P A I b := by
  unfold batchFinish
  rw [add_assoc]
  gcongr
  exact (add_le_add le_rfl (h3_span ha)).trans (h3_compl_le hj)

theorem h3_feas {D : Type} [Inhabited D] (E : Environment D) (P : Protocol D)
    (A : BaseAlgorithm D) (ρ : ℝ≥0) (c d : ℕ) (hA : Eligible E P A ρ c d)
    (I : Instance D) (hI : Valid E I) {R : Finset ℕ} {t : ℝ≥0} {bs : List Batch}
    (h : BatchExecution P A I R t bs) (hR : R ⊆ I.jobs) :
    Feasible E ⟨R, I.data, I.release⟩ (assembled P A I bs) ∧
      ∀ j ∈ R, t ≤ (assembled P A I bs j).start := by
  induction h with
  | done t =>
    exact ⟨⟨fun j hj => absurd hj (Finset.notMem_empty j),
      fun j hj => absurd hj (Finset.notMem_empty j)⟩,
      fun j hj => absurd hj (Finset.notMem_empty j)⟩
  | next R t b rest hne hnd hw hs htail ih =>
    have hJR : b.jobs.toFinset ⊆ R := by rw [hw]; exact Finset.filter_subset _ _
    have hbat := h3_batch E P A ρ c d hA I hI b hne hnd (hJR.trans hR)
    obtain ⟨ihF, ihS⟩ := ih (Finset.sdiff_subset.trans hR)
    have hts : t ≤ b.start := by
      rcases hs with h | h
      · exact h.symm.le
      · exact h.1.le
    have hfin : b.start ≤ batchFinish P A I b := le_self_add
    have hrest : ∀ k ∈ R, k ∉ b.jobs.toFinset →
        batchFinish P A I b ≤ (assembled P A I rest k).start :=
      fun k hk hkJ => ihS k (Finset.mem_sdiff.2 ⟨hk, hkJ⟩)
    refine ⟨⟨fun j hj => ?_, fun j hj k hk hjk a ha c hc hd => ?_⟩, fun j hj => ?_⟩
    · change j ∈ R at hj
      show I.release j ≤ (assembled P A I (b :: rest) j).start ∧
        WellFormed E.resources (assembled P A I (b :: rest) j).profile ∧
        E.legal (I.data j) (assembled P A I (b :: rest) j).profile
      by_cases hjJ : j ∈ b.jobs.toFinset
      · rw [h3_asJ P A I b rest j hjJ]
        obtain ⟨-, hwf, hl⟩ := hbat.1.1 j hjJ
        have hrel : I.release j ≤ b.start := by
          rw [hw] at hjJ; exact (Finset.mem_filter.1 hjJ).2
        exact ⟨hrel.trans le_self_add, hwf, hl⟩
      · rw [h3_asN P A I b rest j hjJ]
        exact ihF.1 j (Finset.mem_sdiff.2 ⟨hj, hjJ⟩)
    · change j ∈ R at hj
      change k ∈ R at hk
      by_cases hjJ : j ∈ b.jobs.toFinset <;> by_cases hkJ : k ∈ b.jobs.toFinset
      · rw [h3_asJ P A I b rest j hjJ] at ha ⊢
        rw [h3_asJ P A I b rest k hkJ] at hc ⊢
        show b.start + _ + a.hi ≤ b.start + _ + c.lo ∨ b.start + _ + c.hi ≤ b.start + _ + a.lo
        simp only [add_assoc]
        rcases hbat.1.2 j hjJ k hkJ hjk a ha c hc hd with h | h
        · left; exact add_le_add le_rfl h
        · right; exact add_le_add le_rfl h
      · rw [h3_asJ P A I b rest j hjJ] at ha ⊢
        rw [h3_asN P A I b rest k hkJ] at hc ⊢
        left
        exact (h3_end P A I b j hjJ a ha).trans ((hrest k hk hkJ).trans le_self_add)
      · rw [h3_asN P A I b rest j hjJ] at ha ⊢
        rw [h3_asJ P A I b rest k hkJ] at hc ⊢
        right
        exact (h3_end P A I b k hkJ c hc).trans ((hrest j hj hjJ).trans le_self_add)
      · rw [h3_asN P A I b rest j hjJ] at ha ⊢
        rw [h3_asN P A I b rest k hkJ] at hc ⊢
        exact ihF.2 j (Finset.mem_sdiff.2 ⟨hj, hjJ⟩) k (Finset.mem_sdiff.2 ⟨hk, hkJ⟩)
          hjk a ha c hc hd
    · by_cases hjJ : j ∈ b.jobs.toFinset
      · rw [h3_asJ P A I b rest j hjJ]
        exact hts.trans le_self_add
      · rw [h3_asN P A I b rest j hjJ]
        exact hts.trans (hfin.trans (hrest j hj hjJ))

theorem h3_cost {D : Type} [Inhabited D] (E : Environment D) (P : Protocol D)
    (A : BaseAlgorithm D) (ρ : ℝ≥0) (c d : ℕ) (hA : Eligible E P A ρ c d) (hρ : 1 ≤ ρ)
    (I : Instance D) (hI : Valid E I) (u : Schedule) (hu : Feasible E I u)
    {R : Finset ℕ} {t : ℝ≥0} {bs : List Batch}
    (h : BatchExecution P A I R t bs) (hR : R ⊆ I.jobs) :
    ∀ σ : ℝ≥0, (∀ j ∈ R, σ ≤ I.release j) → t ≤ σ + ρ * makespan I.jobs u →
      ∀ j ∈ R, completion (assembled P A I bs) j ≤ 2 * ρ * makespan I.jobs u := by
  set M := makespan I.jobs u with hM
  induction h with
  | done t => exact fun _ _ _ j hj => absurd hj (Finset.notMem_empty j)
  | next R t b rest hne hnd hw hs htail ih =>
    intro σ hσ ht
    have hJR : b.jobs.toFinset ⊆ R := by rw [hw]; exact Finset.filter_subset _ _
    have hbat := h3_batch E P A ρ c d hA I hI b hne hnd (hJR.trans hR)
    have hJne : b.jobs.toFinset.Nonempty := List.toFinset_nonempty_iff _ |>.2 hne
    have key := h3_ratio E I ρ hρ _ (hJR.trans hR) hJne _ hbat u hu
    have hfdef : batchFinish P A I b = b.start + makespan b.jobs.toFinset (batchSchedule P A I b) := rfl
    have hboth : makespan b.jobs.toFinset (batchSchedule P A I b) ≤ ρ * M ∧
        batchFinish P A I b ≤ 2 * ρ * M := by
      rcases hs with h | h
      · have k1 := key σ (fun j hj => hσ j (hJR hj))
        rw [hfdef, h]
        constructor
        · exact le_add_self.trans k1
        · calc t + makespan b.jobs.toFinset (batchSchedule P A I b)
              ≤ σ + ρ * M + makespan b.jobs.toFinset (batchSchedule P A I b) := by gcongr
            _ = ρ * M + (σ + makespan b.jobs.toFinset (batchSchedule P A I b)) := by ring
            _ ≤ ρ * M + ρ * M := by gcongr
            _ = 2 * ρ * M := by ring
      · have k1 := key b.start (fun j hj => h.2.1 j (hJR hj))
        rw [hfdef]
        constructor
        · exact le_add_self.trans k1
        · calc b.start + makespan b.jobs.toFinset (batchSchedule P A I b) ≤ ρ * M := k1
            _ ≤ 2 * ρ * M := by
              rw [mul_assoc]; exact le_mul_of_one_le_left zero_le one_le_two
    intro j hj
    by_cases hjJ : j ∈ b.jobs.toFinset
    · unfold completion
      rw [h3_asJ P A I b rest j hjJ]
      show b.start + (batchSchedule P A I b j).start + span (batchSchedule P A I b j).profile ≤ _
      rw [add_assoc]
      refine le_trans ?_ hboth.2
      rw [hfdef]
      exact add_le_add le_rfl (h3_compl_le hjJ)
    · unfold completion
      rw [h3_asN P A I b rest j hjJ]
      refine ih (Finset.sdiff_subset.trans hR) b.start (fun k hk => ?_) ?_ j
        (Finset.mem_sdiff.2 ⟨hj, hjJ⟩)
      · obtain ⟨hkR, hkJ⟩ := Finset.mem_sdiff.1 hk
        rw [hw, Finset.mem_filter] at hkJ
        exact (lt_of_not_ge fun h' => hkJ ⟨hkR, h'⟩).le
      · rw [hfdef]; exact add_le_add le_rfl hboth.1

/-- (H3) the assembled schedule is a 2ρ-approximation. -/
theorem approx {D : Type} [Inhabited D] (E : Environment D) (P : Protocol D)
    (A : BaseAlgorithm D) (ρ : ℝ≥0) (c d : ℕ) (hA : Eligible E P A ρ c d) (hρ : 1 ≤ ρ)
    (I : Instance D) (hI : Valid E I) (bs : List Batch)
    (hb : BatchExecution P A I I.jobs 0 bs) :
    Approx E I (2 * ρ) (assembled P A I bs) := by
  refine ⟨(h3_feas E P A ρ c d hA I hI hb subset_rfl).1, fun u hu => ?_⟩
  exact Finset.sup_le fun j hj =>
    h3_cost E P A ρ c d hA hρ I hI u hu hb subset_rfl 0 (fun _ _ => zero_le) zero_le j hj


theorem me_le_span (p : Profile) (a : Slice) (ha : a ∈ p) : a.hi ≤ span p := by
  unfold span
  induction p with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.1 ha with h | h
    · subst h; exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem pos {D : Type} [Inhabited D] (E : Environment D) (P : Protocol D)
    (A : BaseAlgorithm D) (ρ : ℝ≥0) (c d : ℕ) (hA : Eligible E P A ρ c d)
    (I : Instance D) (hI : Valid E I) :
    ∀ b : Batch, b.jobs ≠ [] → b.jobs.Nodup → b.jobs.toFinset ⊆ I.jobs →
      b.start < batchFinish P A I b := by
  intro b hne hnd hsub
  set B : BatchData D := b.jobs.map (fun j => (j, I.data j)) with hB
  have hBf : B.map Prod.fst = b.jobs := by simp [hB, Function.comp_def]
  have hvalid : ValidBatch E B := by
    refine ⟨by rw [hBf]; exact hnd, ?_⟩
    intro x hx
    simp only [hB, List.mem_map] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    exact hI j (hsub (List.mem_toFinset.2 hj))
  have hBne : B ≠ [] := by simpa [hB] using hne
  obtain ⟨-, -, -, -, hap⟩ := hA.2 B hvalid hBne
  obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil b.jobs hne
  have hjB : j ∈ (batchInstance B).jobs := by
    simp only [batchInstance, hBf]; exact List.mem_toFinset.2 hj
  obtain ⟨-, hwf, -⟩ := hap.1.1 j hjB
  obtain ⟨hpne, hsl⟩ := hwf
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hpne
  have h1 : 0 < a.hi := lt_of_le_of_lt (bot_le : (0:ℝ≥0) ≤ a.lo) (hsl a ha).1
  have h2 : a.hi ≤ completion (baseSchedule P A B) j :=
    (me_le_span _ a ha).trans (le_add_self)
  have h3 : completion (baseSchedule P A B) j ≤ makespan b.jobs.toFinset (batchSchedule P A I b) := by
    unfold makespan batchSchedule
    exact Finset.le_sup (f := completion (baseSchedule P A B)) (List.mem_toFinset.2 hj)
  unfold batchFinish
  exact lt_add_of_pos_right _ (lt_of_lt_of_le h1 (h2.trans h3))

end SH89

theorem solution {V : Type} {D : V → Type} [∀ v, Inhabited (D v)]
    (E : (v : V) → Environment (D v)) (P : (v : V) → Protocol (D v))
    (A : UniformAlgorithm V D) (hP : ∀ v, HonestProcessing (E v) (P v))
    (ρ : V → ℝ≥0) (hρ : ∀ v, 1 ≤ ρ v) (c d : ℕ)
    (hA : ∀ v, Eligible (E v) (P v) (specialize A v) (ρ v) c d) :
    ControllerCausal ∧
    ∀ (v : V) (I : Instance (D v)), Valid (E v) I →
      ∃ (bs : List Batch) (es : List Packet),
        BatchExecution (P v) (specialize A v) I I.jobs 0 bs ∧
        EventsFor (P v) (specialize A v) I bs es ∧
        (controllerRun es).2.1 = bs.map (fun b => (b.start, b.jobs)) ∧
        bs.length ≤ I.jobs.card ∧
        (bs.map (fun b => b.jobs.toFinset)).Pairwise Disjoint ∧
        (bs.flatMap Batch.jobs).toFinset = I.jobs ∧
        computationCost (P v) (specialize A v) I bs es ≤
          I.jobs.card * c * (releasedInputSize (P v) I + 1) ^ d +
            10 * (releasedInputSize (P v) I + 1) ^ 2 ∧
        Approx (E v) I (2 * ρ v) (assembled (P v) (specialize A v) I bs) := by
  refine ⟨SH89.causal, fun v I hI => ?_⟩
  obtain ⟨bs, es, hb, he, hc⟩ := SH89.exists_exec (P v) (specialize A v) I
    (SH89.pos (E v) (P v) (specialize A v) (ρ v) c d (hA v) I hI)
  obtain ⟨h1, h2, h3, -⟩ := SH89.exec_struct hb
  exact ⟨bs, es, hb, he, hc, h1, h2, h3,
    SH89.cost_bound (E v) (P v) (specialize A v) (ρ v) c d (hA v) I hI bs es hb he,
    SH89.approx (E v) (P v) (specialize A v) (ρ v) c d (hA v) (hρ v) I hI bs hb⟩

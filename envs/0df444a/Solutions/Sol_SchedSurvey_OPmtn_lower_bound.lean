-- Prove2me | solution 1 for SchedSurvey.OPmtn.lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:41:20.025463+00:00
-- url     : https://prove2.me/submissions/00448f1d-2666-4b73-bf3a-59453e2f8598

import Mathlib
import Definitions.Def_SchedSurvey_OPmtn_Model

set_option autoImplicit false
open SchedSurvey.OPmtn MeasureTheory

namespace HHSS

/-- union of the half-open intervals of a list of pieces -/
def U {m n : ℕ} : List (Piece m n) → Set ℝ
  | [] => ∅
  | q :: L => Set.Ico q.start q.stop ∪ U L

lemma U_meas {m n : ℕ} (L : List (Piece m n)) : MeasurableSet (U L) := by
  induction L with
  | nil => exact MeasurableSet.empty
  | cons q L ih => exact measurableSet_Ico.union ih

lemma U_sub {m n : ℕ} (T : ℝ) (L : List (Piece m n))
    (hL : ∀ q ∈ L, 0 ≤ q.start ∧ q.start ≤ q.stop ∧ q.stop ≤ T) : U L ⊆ Set.Ico 0 T := by
  induction L with
  | nil => simp [U]
  | cons q L ih =>
    intro x hx
    rcases hx with hx | hx
    · have h := hL q (by simp)
      exact ⟨le_trans h.1 hx.1, lt_of_lt_of_le hx.2 h.2.2⟩
    · exact ih (fun q' hq' => hL q' (by simp [hq'])) hx

lemma U_disj {m n : ℕ} (q : Piece m n) (L : List (Piece m n))
    (h : ∀ q' ∈ L, q.stop ≤ q'.start ∨ q'.stop ≤ q.start)
    (hL : ∀ q ∈ L, q.start ≤ q.stop) (hq : q.start ≤ q.stop) :
    Disjoint (Set.Ico q.start q.stop) (U L) := by
  induction L with
  | nil => simp [U]
  | cons q' L ih =>
    have h1 : Disjoint (Set.Ico q.start q.stop) (Set.Ico q'.start q'.stop) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      rcases h q' (by simp) with h2 | h2
      · linarith [hx.2, hx'.1]
      · linarith [hx.1, hx'.2]
    have h2 := ih (fun q'' hq'' => h q'' (by simp [hq''])) (fun q'' hq'' => hL q'' (by simp [hq'']))
    exact Disjoint.union_right h1 h2

lemma sum_eq_vol {m n : ℕ} (L : List (Piece m n))
    (hL : ∀ q ∈ L, q.start ≤ q.stop)
    (hP : L.Pairwise (fun q q' => q.stop ≤ q'.start ∨ q'.stop ≤ q.start)) :
    ENNReal.ofReal ((L.map (fun q => q.stop - q.start)).sum) = volume (U L) := by
  induction L with
  | nil => simp [U]
  | cons q L ih =>
    rw [List.pairwise_cons] at hP
    have hq := hL q (by simp)
    have hL' : ∀ q ∈ L, q.start ≤ q.stop := fun q' hq' => hL q' (by simp [hq'])
    have hs : 0 ≤ (L.map (fun q => q.stop - q.start)).sum := by
      apply List.sum_nonneg
      intro x hx
      obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hx
      linarith [hL' q' hq']
    have hdisj := U_disj q L hP.1 hL' hq
    simp only [List.map_cons, List.sum_cons, U]
    rw [ENNReal.ofReal_add (by linarith) hs, ih hL' hP.2,
      measure_union hdisj (U_meas L), Real.volume_Ico]

lemma disj_total {m n : ℕ} (T : ℝ) (hT : 0 ≤ T) (L : List (Piece m n))
    (hL : ∀ q ∈ L, 0 ≤ q.start ∧ q.start ≤ q.stop ∧ q.stop ≤ T)
    (hP : L.Pairwise (fun q q' => q.stop ≤ q'.start ∨ q'.stop ≤ q.start)) :
    (L.map (fun q => q.stop - q.start)).sum ≤ T := by
  have h1 := sum_eq_vol L (fun q hq => (hL q hq).2.1) hP
  have h2 : volume (U L) ≤ volume (Set.Ico (0:ℝ) T) := measure_mono (U_sub T L hL)
  rw [← h1, Real.volume_Ico, sub_zero] at h2
  exact (ENNReal.ofReal_le_ofReal_iff hT).mp h2

lemma split_sum {m n : ℕ} {β : Type} [Fintype β] [DecidableEq β] (a : Piece m n → Prop) [DecidablePred a]
    (κ : Piece m n → β) (f : Piece m n → ℝ) (L : List (Piece m n)) :
    ∑ b : β, ((L.filter (fun q => decide (a q ∧ κ q = b))).map f).sum
      = ((L.filter (fun q => decide (a q))).map f).sum := by
  induction L with
  | nil => simp
  | cons q L ih =>
    have h : ∀ b : β, ((List.filter (fun q => decide (a q ∧ κ q = b)) (q :: L)).map f).sum
        = (if a q ∧ κ q = b then f q else 0) + ((L.filter (fun q => decide (a q ∧ κ q = b))).map f).sum := by
      intro b
      by_cases hb : a q ∧ κ q = b
      · simp [List.filter_cons, hb]
      · simp [List.filter_cons, hb]
    simp_rw [h]
    rw [Finset.sum_add_distrib, ih]
    by_cases ha : a q
    · have : ∑ b : β, (if a q ∧ κ q = b then f q else 0) = f q := by
        simp [ha]
      rw [this]
      simp [List.filter_cons, ha]
    · have : ∑ b : β, (if a q ∧ κ q = b then f q else 0) = 0 := by
        simp [ha]
      rw [this]
      simp [List.filter_cons, ha]

end HHSS

theorem solution {m n : ℕ} (P : Fin m → Fin n → ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (S : List (Piece m n)) (hS : IsFeasible P S) (T : ℝ) (hT : 0 ≤ T)
    (hST : CompletesBy S T) :
    (∀ i, rowSum P i ≤ T) ∧ ∀ j, colSum P j ≤ T := by
  obtain ⟨h1, h2, h3⟩ := hS
  have hbound : ∀ q ∈ S, 0 ≤ q.start ∧ q.start ≤ q.stop ∧ q.stop ≤ T :=
    fun q hq => ⟨(h1 q hq).1, (h1 q hq).2, hST q hq⟩
  constructor
  · intro i
    have e : rowSum P i = ((S.filter (fun q => decide (q.mach = i))).map (fun q => q.stop - q.start)).sum := by
      unfold rowSum
      simp_rw [← h3 i]
      exact HHSS.split_sum (fun q => q.mach = i) (fun q => q.job) _ S
    rw [e]
    apply HHSS.disj_total T hT
    · intro q hq
      exact hbound q (List.mem_of_mem_filter hq)
    · have := h2.filter (fun q => decide (q.mach = i))
      refine List.Pairwise.imp_of_mem ?_ this
      intro a b ha hb hab
      have ha' := (List.mem_filter.mp ha).2
      have hb' := (List.mem_filter.mp hb).2
      simp only [decide_eq_true_eq] at ha' hb'
      exact hab (Or.inl (ha'.trans hb'.symm))
  · intro j
    have e : colSum P j = ((S.filter (fun q => decide (q.job = j))).map (fun q => q.stop - q.start)).sum := by
      unfold colSum
      have hc : ∀ i, P i j = ((S.filter (fun q => decide (q.job = j ∧ q.mach = i))).map
          (fun q => q.stop - q.start)).sum := by
        intro i
        rw [← h3 i j]
        congr 2
        exact List.filter_congr (fun q _ => by simp [and_comm])
      simp_rw [hc]
      exact HHSS.split_sum (fun q => q.job = j) (fun q => q.mach) _ S
    rw [e]
    apply HHSS.disj_total T hT
    · intro q hq
      exact hbound q (List.mem_of_mem_filter hq)
    · have := h2.filter (fun q => decide (q.job = j))
      refine List.Pairwise.imp_of_mem ?_ this
      intro a b ha hb hab
      have ha' := (List.mem_filter.mp ha).2
      have hb' := (List.mem_filter.mp hb).2
      simp only [decide_eq_true_eq] at ha' hb'
      exact hab (Or.inr (ha'.trans hb'.symm))

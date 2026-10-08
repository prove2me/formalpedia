-- Prove2me | solution 1 for WhittFLT.FirstPassage.firstPassage_mem
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:52:01.792813+00:00
-- url     : https://prove2.me/submissions/786e7452-b640-488c-9c38-03d0cad80051

import Mathlib
import Definitions.Def_WhittFLT_FirstPassage_FirstPassage

open Set WhittFLT.FirstPassage

theorem passage_set_nonempty (x : ℝ → ℝ) (hx : InE x) (t : ℝ) :
    {s : ℝ | 0 ≤ s ∧ t < x s}.Nonempty := by
  obtain ⟨y, ⟨s, hs, rfl⟩, hy⟩ := not_bddAbove_iff.mp hx.2.1 t
  exact ⟨s, hs, hy⟩

theorem passage_nonneg (x : ℝ → ℝ) (hx : InE x) (t : ℝ) :
    0 ≤ firstPassage x t := by
  exact le_csInf (passage_set_nonempty x hx t) (fun s hs => hs.1)

theorem passage_monotone (x : ℝ → ℝ) (hx : InE x) : Monotone (firstPassage x) := by
  intro a b hab
  apply csInf_le_csInf
  · exact ⟨0, fun s hs => hs.1⟩
  · exact passage_set_nonempty x hx b
  · intro s hs
    exact ⟨hs.1, hab.trans_lt hs.2⟩



open Filter Topology

theorem passage_right_continuous (x : ℝ → ℝ) (hx : InE x) (t : ℝ) :
    ContinuousWithinAt (firstPassage x) (Ici t) t := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact ha.trans_le (passage_monotone x hx hy)
  · intro b hb
    obtain ⟨s, hs, hsb⟩ := exists_lt_of_csInf_lt (passage_set_nonempty x hx t) hb
    have hev : ∀ᶠ y in 𝓝[Ici t] t, y < x s :=
      (eventually_lt_nhds hs.2).filter_mono nhdsWithin_le_nhds
    filter_upwards [hev] with y hy
    exact (csInf_le (show BddBelow {s : ℝ | 0 ≤ s ∧ y < x s} from ⟨0, fun s hs => hs.1⟩)
      (show s ∈ {s : ℝ | 0 ≤ s ∧ y < x s} from ⟨hs.1, hy⟩)).trans_lt hsb

theorem passage_cadlag (x : ℝ → ℝ) (hx : InE x) :
    WhittFLT.Composition.IsCadlagOn (Ici 0) (firstPassage x) := by
  intro t ht
  constructor
  · exact (passage_right_continuous x hx t).mono inter_subset_right
  · refine ⟨sSup (firstPassage x '' Iio t), ?_⟩
    exact ((passage_monotone x hx).tendsto_nhdsLT t).mono_left
      (nhdsWithin_mono _ inter_subset_right)



theorem cadlag_locally_bddAbove (x : ℝ → ℝ)
    (hx : WhittFLT.Composition.IsCadlagOn (Ici 0) x) (t : ℝ) (ht : 0 ≤ t) :
    ∃ M : ℝ, ∀ᶠ s in 𝓝[Ici 0] t, x s ≤ M := by
  obtain ⟨hc, l, hl⟩ := hx t ht
  have hr : ∀ᶠ s in 𝓝[Ici 0 ∩ Ici t] t, x s < x t + 1 :=
    hc.eventually (gt_mem_nhds (by linarith : x t < x t + 1))
  have hl' : ∀ᶠ s in 𝓝[Ici 0 ∩ Iio t] t, x s < l + 1 :=
    hl.eventually (gt_mem_nhds (by linarith : l < l + 1))
  refine ⟨max (x t + 1) (l + 1), ?_⟩
  have hu : (Ici 0 ∩ Ici t) ∪ (Ici 0 ∩ Iio t) = Ici 0 := by
    ext s
    simp only [mem_union, mem_inter_iff, mem_Ici, mem_Iio]
    constructor
    · tauto
    · intro hs
      rcases le_or_gt t s with h | h
      · exact Or.inl ⟨hs, h⟩
      · exact Or.inr ⟨hs, h⟩
  rw [← hu, nhdsWithin_union, Filter.eventually_sup]
  exact ⟨hr.mono (fun s hs => hs.le.trans (le_max_left _ _)),
    hl'.mono (fun s hs => hs.le.trans (le_max_right _ _))⟩

theorem cadlag_compact_bddAbove (x : ℝ → ℝ)
    (hx : WhittFLT.Composition.IsCadlagOn (Ici 0) x) (a : ℝ) :
    BddAbove (x '' Icc 0 a) := by
  classical
  choose M hM using fun t : Icc (0 : ℝ) a => cadlag_locally_bddAbove x hx t t.2.1
  obtain ⟨F, hF⟩ := isCompact_Icc.elim_nhdsWithin_subcover'
    (fun t ht => {s | x s ≤ M ⟨t, ht⟩})
    (fun t ht => (hM ⟨t, ht⟩).filter_mono (nhdsWithin_mono _ Icc_subset_Ici_self))
  obtain ⟨B, hB⟩ := (F.finite_toSet.image M).bddAbove
  refine ⟨B, ?_⟩
  rintro y ⟨s, hs, rfl⟩
  obtain ⟨t, ht, hst⟩ := mem_iUnion₂.mp (hF hs)
  exact hst.trans (hB (mem_image_of_mem M ht))

theorem passage_unbounded (x : ℝ → ℝ) (hx : InE x) :
    ¬ BddAbove (firstPassage x '' Ici 0) := by
  rintro ⟨R, hR⟩
  obtain ⟨B, hB⟩ := cadlag_compact_bddAbove x hx.1 (max R 0 + 1)
  have hp : firstPassage x (max B 0) ≤ R := hR (mem_image_of_mem _ (le_max_right B 0))
  have hlt : firstPassage x (max B 0) < max R 0 + 1 := by linarith [le_max_left R 0]
  obtain ⟨s, hs, hsa⟩ := exists_lt_of_csInf_lt (passage_set_nonempty x hx (max B 0)) hlt
  have hb : x s ≤ B := hB (mem_image_of_mem _ (show s ∈ Icc 0 (max R 0 + 1) from ⟨hs.1, hsa.le⟩))
  linarith [hs.2, le_max_left B 0]



theorem solution (x : ℝ → ℝ) (hx : InE x) :
    InE (firstPassage x) ∧ MonotoneOn (firstPassage x) (Ici 0) ∧
      MapsTo (firstPassage x) (Ici 0) (Ici 0) := by
  exact ⟨⟨passage_cadlag x hx, passage_unbounded x hx, passage_nonneg x hx 0⟩,
    (passage_monotone x hx).monotoneOn _, fun t ht => passage_nonneg x hx t⟩

#print axioms solution


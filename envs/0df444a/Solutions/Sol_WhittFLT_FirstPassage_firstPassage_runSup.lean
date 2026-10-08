-- Prove2me | solution 1 for WhittFLT.FirstPassage.firstPassage_runSup
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:59:04.736255+00:00
-- url     : https://prove2.me/submissions/60cebeff-9f66-4574-a936-d9408c29ec76

import Mathlib
import Definitions.Def_WhittFLT_FirstPassage_FirstPassage

open Set Filter Topology WhittFLT.FirstPassage WhittFLT.Reflection

private theorem cadlag_bound (x : ℝ → ℝ) (hx : InE x) (t : ℝ) :
    BddAbove (x '' Icc 0 t) := by
  have hl (a : ℝ) (ha : 0 ≤ a) :
      ∃ B : ℝ, ∀ᶠ u in 𝓝[Ici 0] a, x u ≤ B := by
    obtain ⟨l, hleft⟩ := (hx.1 a ha).2
    obtain ⟨Bl, hBl⟩ := hleft.isBoundedUnder_le
    obtain ⟨Br, hBr⟩ := (hx.1 a ha).1.isBoundedUnder_le
    refine ⟨max Bl Br, ?_⟩
    rw [← nhdsWithinLT_sup_nhdsWithinGE a, eventually_sup]
    constructor
    · filter_upwards [hBl] with u hu using hu.trans (le_max_left _ _)
    · filter_upwards [hBr] with u hu using hu.trans (le_max_right _ _)
  apply isCompact_Icc.induction_on (p := fun s => BddAbove (x '' s))
  · simp
  · intro s u hsu hu
    exact hu.mono (image_mono hsu)
  · intro s u hs hu
    simpa [image_union] using hs.union hu
  · intro a ha
    obtain ⟨B, hB⟩ := hl a ha.1
    have hB' : ∀ᶠ u in 𝓝[Icc 0 t] a, x u ≤ B :=
      hB.filter_mono (nhdsWithin_mono a (fun _ h => h.1))
    exact ⟨{u | x u ≤ B}, hB', B, by rintro _ ⟨u, hu, rfl⟩; exact hu⟩

private theorem sup_ge (x : ℝ → ℝ) (hx : InE x) {t s : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) : x s ≤ runSup x t :=
  le_csSup (cadlag_bound x hx t) ⟨s, ⟨hs, hst⟩, rfl⟩

private theorem sup_mono (x : ℝ → ℝ) (hx : InE x) :
    MonotoneOn (runSup x) (Ici 0) := by
  intro a ha b hb hab
  change sSup (x '' Icc 0 a) ≤ runSup x b
  apply csSup_le (s := x '' Icc 0 a) ⟨x 0, ⟨0, ⟨le_rfl, ha⟩, rfl⟩⟩
  rintro y ⟨s, hs, rfl⟩
  exact sup_ge x hx hs.1 (hs.2.trans hab)

private theorem sup_right (x : ℝ → ℝ) (hx : InE x) (t : ℝ) (ht : 0 ≤ t) :
    ContinuousWithinAt (runSup x) (Ici 0 ∩ Ici t) t := by
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousWithinAt_iff.mp (hx.1 t ht).1 (ε / 2) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro u hu hut
  have htu : runSup x t ≤ runSup x u := sup_mono x hx ht hu.1 hu.2
  have hupper : runSup x u ≤ runSup x t + ε / 2 := by
    change sSup (x '' Icc 0 u) ≤ runSup x t + ε / 2
    apply csSup_le (s := x '' Icc 0 u) ⟨x 0, ⟨0, ⟨le_rfl, hu.1⟩, rfl⟩⟩
    rintro y ⟨s, hs, rfl⟩
    by_cases hst : s ≤ t
    · have := sup_ge x hx hs.1 hst
      linarith
    · have hts : t ≤ s := le_of_lt (lt_of_not_ge hst)
      have hdist : dist s t < δ := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hts)]
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hu.2)] at hut
        linarith [hs.2]
      have hb := hd ⟨hs.1, hts⟩ hdist
      rw [Real.dist_eq] at hb
      have hxt := sup_ge x hx ht le_rfl
      have := (abs_lt.mp hb).2
      linarith
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr htu)]
  linarith

private theorem sup_cadlag (x : ℝ → ℝ) (hx : InE x) :
    WhittFLT.Composition.IsCadlagOn (Ici 0) (runSup x) := by
  intro t ht
  refine ⟨sup_right x hx t ht, ?_⟩
  by_cases hpos : 0 < t
  · let S := runSup x '' Ioo 0 t
    have hne : (Ioo 0 t).Nonempty := nonempty_Ioo.mpr hpos
    have hb : BddAbove S := by
      refine ⟨runSup x t, ?_⟩
      rintro y ⟨s, hs, rfl⟩
      exact sup_mono x hx (le_of_lt hs.1) ht (le_of_lt hs.2)
    have hm : MonotoneOn (runSup x) (Ioo 0 t) :=
      (sup_mono x hx).mono (fun _ h => le_of_lt h.1)
    refine ⟨sSup S, ?_⟩
    exact (hm.tendsto_nhdsWithin_Ioo_left hne hb).mono_left
      (nhdsWithin_mono t (fun _ h => h.2))
  · have he : Ici 0 ∩ Iio t = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro a ha
      have h1 : 0 ≤ a := ha.1
      have h2 : a < t := ha.2
      linarith
    refine ⟨0, ?_⟩
    simp [he]

private theorem passage_ne (x : ℝ → ℝ) (hx : InE x) (t : ℝ) :
    {s : ℝ | 0 ≤ s ∧ t < x s}.Nonempty := by
  obtain ⟨y, ⟨s, hs, rfl⟩, hy⟩ := not_bddAbove_iff.mp hx.2.1 t
  exact ⟨s, hs, hy⟩
private theorem passage_bdd (x : ℝ → ℝ) (t : ℝ) :
    BddBelow {s : ℝ | 0 ≤ s ∧ t < x s} := ⟨0, fun _ h => h.1⟩

theorem solution (x : ℝ → ℝ) (hx : InE x) :
    InE (WhittFLT.Reflection.runSup x) ∧ firstPassage (WhittFLT.Reflection.runSup x) = firstPassage x := by
  have hE : InE (runSup x) := by
    refine ⟨sup_cadlag x hx, ?_, ?_⟩
    · intro hb
      obtain ⟨B, hB⟩ := hb
      apply hx.2.1
      refine ⟨B, ?_⟩
      rintro y ⟨s, hs, rfl⟩
      exact (sup_ge x hx hs le_rfl).trans (hB ⟨s, hs, rfl⟩)
    · exact hx.2.2.trans (sup_ge x hx le_rfl le_rfl)
  refine ⟨hE, ?_⟩
  funext t
  apply le_antisymm
  · apply le_csInf (passage_ne x hx t)
    intro s hs
    exact csInf_le (passage_bdd (runSup x) t) ⟨hs.1, hs.2.trans_le (sup_ge x hx hs.1 le_rfl)⟩
  · apply le_csInf (passage_ne (runSup x) hE t)
    intro s hs
    have hne : (x '' Icc 0 s).Nonempty := ⟨x 0, ⟨0, ⟨le_rfl, hs.1⟩, rfl⟩⟩
    obtain ⟨y, ⟨u, hu, rfl⟩, hy⟩ := exists_lt_of_lt_csSup hne hs.2
    exact (csInf_le (passage_bdd x t) ⟨hu.1, hy⟩).trans hu.2

#print axioms solution

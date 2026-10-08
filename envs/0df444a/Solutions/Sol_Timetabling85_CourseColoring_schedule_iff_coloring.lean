-- Prove2me | solution 1 for Timetabling85.CourseColoring.schedule_iff_coloring
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T01:59:29.597226+00:00
-- url     : https://prove2.me/submissions/2f5711f4-6850-4f65-bfed-b0804f522bd9

import Definitions.Def_Timetabling85_CourseColoring_CSUP

open Timetabling85.CourseColoring

private theorem feasible_iff_valid {q r p : ℕ} (I : CourseInstance q r)
    (s : I.Lecture → Fin p) :
    I.IsFeasibleSchedule p s ↔
      ∀ {l l' : I.Lecture}, I.Conflict l l' → s l ≠ s l' := by
  constructor
  · intro hs l l' hc
    rcases l with ⟨b, a⟩
    rcases l' with ⟨b', a'⟩
    rcases hc with ⟨hbb, hll⟩ | ⟨hbb, i, hbi, hb'i⟩
    · dsimp at hbb
      subst b'
      apply hs.1 b a a'
      intro ha
      subst a'
      exact hll rfl
    · exact hs.2 i b b' hbi hb'i hbb a a'
  · intro hv
    constructor
    · intro b a a' ha
      apply hv
      refine Or.inl ⟨rfl, ?_⟩
      intro he
      apply ha
      cases he
      rfl
    · intro i b b' hbi hb'i hbb a a'
      exact hv (Or.inr ⟨hbb, i, hbi, hb'i⟩)

theorem solution {q r : ℕ} (I : CourseInstance q r) (p : ℕ) :
    (∀ s : I.Lecture → Fin p,
      I.IsFeasibleSchedule p s ↔ ∃ c : I.lectureGraph.Coloring (Fin p), ⇑c = s) ∧
    ((∃ s : I.Lecture → Fin p, I.IsFeasibleSchedule p s) ↔ I.lectureGraph.Colorable p) := by
  have correspondence (s : I.Lecture → Fin p) :
      I.IsFeasibleSchedule p s ↔ ∃ c : I.lectureGraph.Coloring (Fin p), ⇑c = s := by
    constructor
    · intro hs
      exact ⟨SimpleGraph.Coloring.mk s ((feasible_iff_valid I s).mp hs), rfl⟩
    · rintro ⟨c, rfl⟩
      exact (feasible_iff_valid I c).mpr (fun h => c.valid h)
  refine ⟨correspondence, ?_⟩
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨c, _⟩ := (correspondence s).mp hs
    exact ⟨c⟩
  · rintro ⟨c⟩
    exact ⟨c, (correspondence c).mpr ⟨c, rfl⟩⟩

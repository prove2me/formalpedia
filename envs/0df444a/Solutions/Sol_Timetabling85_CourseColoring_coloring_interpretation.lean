-- Prove2me | solution 1 for Timetabling85.CourseColoring.coloring_interpretation
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:01:15.675546+00:00
-- url     : https://prove2.me/submissions/97910cd5-32ff-4525-9b9f-14629367c495

import Theorems.Thm_Timetabling85_CourseColoring_schedule_iff_coloring

open Timetabling85.CourseColoring

theorem solution {q r p : ℕ} (P : CSUP q r p) :
    (∀ c : P.csupGraph.Coloring (Fin p), ∃ s : P.Lecture → Fin p, P.IsFeasible s ∧
      ∀ (l : P.Lecture) (k : Fin p), s l = k ↔ c (Sum.inl l) = c (Sum.inr k)) ∧
    (∀ s : P.Lecture → Fin p, P.IsFeasible s → ∃ c : P.csupGraph.Coloring (Fin p),
      ∀ (l : P.Lecture) (k : Fin p), s l = k ↔ c (Sum.inl l) = c (Sum.inr k)) := by
  classical
  constructor
  · intro c
    have hinj : Function.Injective (fun k : Fin p => c (Sum.inr k)) := by
      intro k k' he
      by_contra hne
      exact c.valid (show P.csupGraph.Adj (Sum.inr k) (Sum.inr k') from hne) he
    let e : Fin p ≃ Fin p := Equiv.ofBijective (fun k => c (Sum.inr k))
      ⟨hinj, Finite.surjective_of_injective hinj⟩
    let s : P.Lecture → Fin p := fun l => e.symm (c (Sum.inl l))
    have hscolor (l : P.Lecture) : c (Sum.inr (s l)) = c (Sum.inl l) :=
      e.apply_symm_apply _
    have hrel (l : P.Lecture) (k : Fin p) :
        s l = k ↔ c (Sum.inl l) = c (Sum.inr k) := by
      constructor
      · rintro rfl
        exact (hscolor l).symm
      · intro he
        apply hinj
        exact (hscolor l).trans he
    have hvalid : ∀ {l l' : P.Lecture}, P.Conflict l l' → s l ≠ s l' := by
      intro l l' hc he
      apply c.valid (show P.csupGraph.Adj (Sum.inl l) (Sum.inl l') from hc)
      rw [← hscolor l, ← hscolor l', he]
    have hsched : P.toCourseInstance.IsFeasibleSchedule p s :=
      ((schedule_iff_coloring P.toCourseInstance p).1 s).mpr
        ⟨SimpleGraph.Coloring.mk s hvalid, rfl⟩
    refine ⟨s, ⟨hsched, ?_, ?_⟩, hrel⟩
    · intro l hu
      exact c.valid (show P.csupGraph.Adj (Sum.inl l) (Sum.inr (s l)) from
        Or.inl hu) (hscolor l).symm
    · intro l k hk
      by_contra hsk
      exact c.valid (show P.csupGraph.Adj (Sum.inl l) (Sum.inr (s l)) from
        Or.inr ⟨k, hk, hsk⟩) (hscolor l).symm
  · intro s hs
    obtain ⟨lc, hlc⟩ := ((schedule_iff_coloring P.toCourseInstance p).1 s).mp hs.1
    have hcross (l : P.Lecture) (k : Fin p) (h : P.LecturePeriodAdj l k) :
        s l ≠ k := by
      rcases h with hu | ⟨kb, hb, hkk⟩
      · intro he
        apply hs.2.1 l
        simpa only [he] using hu
      · rw [hs.2.2 l kb hb]
        exact Ne.symm hkk
    let f : P.Lecture ⊕ Fin p → Fin p := Sum.elim s id
    have hf : ∀ {x y}, P.csupGraph.Adj x y → f x ≠ f y := by
      intro x y h
      rcases x with l | k <;> rcases y with l' | k'
      · change s l ≠ s l'
        simpa only [← hlc] using lc.valid h
      · exact hcross l k' h
      · exact Ne.symm (hcross l' k h)
      · exact h
    exact ⟨SimpleGraph.Coloring.mk f hf, fun _ _ => Iff.rfl⟩

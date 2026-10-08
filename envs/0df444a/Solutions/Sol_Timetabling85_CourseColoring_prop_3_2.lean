-- Prove2me | solution 1 for Timetabling85.CourseColoring.prop_3_2
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:00:33.877447+00:00
-- url     : https://prove2.me/submissions/2aed6678-013f-4fce-a99d-b7cbd7c7c75c

import Definitions.Def_Timetabling85_CourseColoring_CSUP

open Timetabling85.CourseColoring

theorem solution {V : Type*} {p : ℕ} (H : SimpleGraph (V ⊕ Fin p))
    (pc : V → Option (Fin p))
    (hclique : ∀ k k' : Fin p, k ≠ k' → H.Adj (Sum.inr k) (Sum.inr k'))
    (hcons_period : ∀ (v : V) (k : Fin p), pc v = some k →
      ¬ H.Adj (Sum.inl v) (Sum.inr k))
    (hcons_lecture : ∀ (v v' : V) (k : Fin p), pc v = some k → pc v' = some k →
      ¬ H.Adj (Sum.inl v) (Sum.inl v')) :
    (∃ c : H.Coloring (Fin p), ∀ (v : V) (k : Fin p), pc v = some k →
        c (Sum.inl v) = c (Sum.inr k)) ↔
      (removePrecolored H pc).Colorable p := by
  classical
  constructor
  · rintro ⟨c, hpc⟩
    have hadded : ∀ {x y}, AddedEdge H pc x y →
        c (survivorEmb pc x) ≠ c (survivorEmb pc y) := by
      intro x y h
      cases x with
      | inl u =>
        cases y with
        | inl v => exact False.elim h
        | inr k =>
          obtain ⟨v, hv, hadj⟩ := h
          change c (Sum.inl u.val) ≠ c (Sum.inr k)
          rw [← hpc v k hv]
          exact c.valid hadj
      | inr k => cases y <;> exact False.elim h
    refine ⟨SimpleGraph.Coloring.mk (fun x => c (survivorEmb pc x)) ?_⟩
    intro x y h
    rcases h with h | h | h
    · exact c.valid h
    · exact hadded h
    · exact Ne.symm (hadded h)
  · rintro ⟨d⟩
    let f : V ⊕ Fin p → Fin p := fun x =>
      match x with
      | Sum.inl v =>
        match h : pc v with
        | none => d (Sum.inl ⟨v, h⟩)
        | some k => d (Sum.inr k)
      | Sum.inr k => d (Sum.inr k)
    have fnone (v : V) (hv : pc v = none) :
        f (Sum.inl v) = d (Sum.inl ⟨v, hv⟩) := by
      dsimp only [f]
      split <;> simp_all
    have fsome (v : V) (k : Fin p) (hv : pc v = some k) :
        f (Sum.inl v) = d (Sum.inr k) := by
      dsimp only [f]
      split <;> simp_all
    have hcross (v : V) (k : Fin p) (h : H.Adj (Sum.inl v) (Sum.inr k)) :
        f (Sum.inl v) ≠ f (Sum.inr k) := by
      cases hv : pc v with
      | none =>
        rw [fnone v hv]
        exact d.valid (Or.inl h)
      | some j =>
        rw [fsome v j hv]
        apply d.valid
        apply Or.inl
        apply hclique
        intro he
        subst k
        exact hcons_period v j hv h
    have hf : ∀ {x y}, H.Adj x y → f x ≠ f y := by
      intro x y h
      rcases x with v | i <;> rcases y with w | j
      · cases hv : pc v with
        | none =>
          cases hw : pc w with
          | none =>
            rw [fnone v hv, fnone w hw]
            exact d.valid (Or.inl h)
          | some j =>
            rw [fnone v hv, fsome w j hw]
            exact d.valid (Or.inr (Or.inl ⟨w, hw, h⟩))
        | some i =>
          cases hw : pc w with
          | none =>
            rw [fsome v i hv, fnone w hw]
            apply Ne.symm
            exact d.valid (Or.inr (Or.inl ⟨v, hv, h.symm⟩))
          | some j =>
            rw [fsome v i hv, fsome w j hw]
            apply d.valid
            apply Or.inl
            apply hclique
            intro he
            subst j
            exact hcons_lecture v w i hv hw h
      · exact hcross v j h
      · exact Ne.symm (hcross w i h.symm)
      · exact d.valid (Or.inl h)
    refine ⟨SimpleGraph.Coloring.mk f hf, ?_⟩
    intro v k hv
    exact fsome v k hv

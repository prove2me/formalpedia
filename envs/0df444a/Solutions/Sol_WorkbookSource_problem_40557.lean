-- Prove2me | solution 1 for WorkbookSource.problem_40557
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:43:49.018857+00:00
-- url     : https://prove2.me/submissions/828f35e6-bfd3-4769-a33a-d894ba08e77b

/- InternLM Lean-Workbook, lean_workbook_40557, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y : ℝ) : (2*x+6+2*y=0 ∧ 4*y+2+2*x=0) ↔ (x = -5 ∧ y = 2)  := by
  first
  | solve
    | constructor
      · rintro ⟨h1,h2⟩
        constructor <;> linarith
      · rintro ⟨rfl,rfl⟩
        norm_num
  | solve
    | constructor
      intro h
      exact ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩
      rintro ⟨rfl, rfl⟩
      constructor <;> linarith
  | solve
    | exact ⟨fun ⟨h₁, h₂⟩ ↦ ⟨by linarith, by linarith⟩, fun ⟨h₁, h₂⟩ ↦ ⟨by linarith, by linarith⟩⟩
  | solve
    | constructor
      intro h
      refine' ⟨_, _⟩
      linarith [h.1, h.2]
      linarith [h.1, h.2]
      rintro ⟨rfl, rfl⟩
      norm_num
  | solve
    | constructor
      intro h
      obtain ⟨h1, h2⟩ := h
      constructor <;> linarith
      rintro ⟨rfl, rfl⟩
      constructor <;> linarith
  | solve
    | constructor
      rintro ⟨h₁, h₂⟩
      refine' ⟨_, _⟩
      linarith [h₁, h₂]
      linarith [h₁, h₂]
      rintro ⟨rfl, rfl⟩
      norm_num
  | solve
    | constructor
      · rintro ⟨h1,h2⟩
        constructor <;> linarith
      · rintro ⟨rfl,rfl⟩
        norm_num
  | solve
    | constructor
      intro h
      constructor
      linarith [h.1, h.2]
      linarith [h.1, h.2]
      rintro ⟨h1, h2⟩
      constructor <;> linarith
  | solve
    | constructor
      intro h
      constructor
      linarith [h.1, h.2]
      linarith [h.1, h.2]
      rintro ⟨rfl, rfl⟩
      constructor <;> linarith
  | solve
    | constructor
      rintro ⟨h1, h2⟩
      constructor
      linarith
      linarith
      rintro ⟨rfl, rfl⟩
      constructor <;> linarith
  | solve
    | constructor
      · rintro ⟨h1, h2⟩
        constructor
        · linarith
        · linarith
      · rintro ⟨rfl, rfl⟩
        norm_num
  | solve
    | constructor
      rintro ⟨h1,h2⟩
      constructor
      linarith
      linarith
      rintro ⟨rfl,rfl⟩
      constructor <;> linarith
  | solve
    | apply Iff.intro
      intro h
      apply And.intro
      linarith [h.1, h.2]
      linarith [h.1, h.2]
      rintro ⟨h1, h2⟩
      constructor <;> linarith
  | solve
    | constructor
      · rintro ⟨h₁, h₂⟩
        constructor <;> linarith
      rintro ⟨rfl, rfl⟩
      norm_num
  | solve
    | constructor
      · rintro ⟨h₁, h₂⟩
        refine' ⟨_, _⟩
        · linarith
        · linarith
      · rintro ⟨rfl, rfl⟩
        norm_num
  | solve
    | constructor
      intro h
      constructor
      linarith [h.1, h.2]
      linarith [h.1, h.2]
      rintro ⟨h₁, h₂⟩
      constructor <;> linarith
  | solve
    | constructor
      intro h
      cases' h with h1 h2
      constructor
      linarith
      linarith
      rintro ⟨rfl, rfl⟩
      norm_num
  | solve
    | constructor
      intro h
      obtain ⟨h1, h2⟩ := h
      constructor
      linarith
      linarith
      rintro ⟨rfl, rfl⟩
      norm_num
  | solve
    | constructor
      rintro ⟨h1, h2⟩
      refine' ⟨_, _⟩
      linarith
      linarith
      rintro ⟨rfl, rfl⟩
      norm_num
  | solve
    | exact ⟨fun h => ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩, fun h => ⟨by linarith, by linarith⟩⟩
  | solve
    | constructor
      rintro ⟨h₁, h₂⟩
      apply And.intro
      linarith [h₁, h₂]
      linarith [h₁, h₂]
      rintro ⟨h₁, h₂⟩
      constructor <;> linarith
  | solve
    | constructor
      rintro ⟨h₁, h₂⟩
      constructor <;> linarith [h₁, h₂]
      rintro ⟨rfl, rfl⟩
      norm_num
  | solve
    | constructor
      rintro ⟨h₁, h₂⟩
      constructor
      linarith
      linarith
      rintro ⟨rfl, rfl⟩
      constructor <;> linarith
  | solve
    | simp [add_assoc]
      exact ⟨fun h ↦ ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩, fun h ↦ ⟨by linarith, by linarith⟩⟩
  | solve
    | constructor
      intro h
      obtain ⟨h1, h2⟩ := h
      constructor
      linarith
      linarith
      rintro ⟨rfl, rfl⟩
      constructor <;> linarith
  | solve
    | constructor
      intro h
      constructor
      linarith [h.1, h.2]
      linarith [h.1, h.2]
      rintro ⟨rfl, rfl⟩
      exact ⟨by norm_num, by norm_num⟩
  | solve
    | constructor
      intro h
      constructor <;> linarith [h.1, h.2]
      rintro ⟨h1, h2⟩
      constructor <;> linarith
example : (∀ (x y : ℝ), (2*x+6+2*y=0 ∧ 4*y+2+2*x=0) ↔ (x = -5 ∧ y = 2)) := @solution
#print axioms solution

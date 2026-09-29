-- Prove2me | solution 1 for R03OrientationWordsM6.orientation_count
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T01:34:49.345798+00:00
-- url     : https://prove2.me/submissions/1a0d1e3c-478e-4d60-a5ea-c3eee430c8a1

import Mathlib.Data.Fintype.Pi
import Definitions.Def_r03_defs_67e8a31036_m6_OrientationWords

/- Candidate-only orientation-word algebra, NOT a graph or root theorem.
A nontrivial alternating component has k+1 virtual matching edges. A bit
chooses which adjacent ordinary edge receives its old center. Each ordinary
edge must receive exactly one center. k=0 includes a labelled parallel pair,
whose physical lift is a triangle. Common matching edges are not components.
The translation from graphs to this encoding requires separate review. -/
namespace R03OrientationWordsM6

theorem receive_one_iff (a b : Bool) : receive a b = 1 ↔ a = b := by
  cases a <;> cases b <;> decide

theorem word_constant (k : Nat) (f : Fin (k+1) → Bool) (h : Feasible k f) :
    ∀ i, f i = f 0 := by
  intro i
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih => exact ((receive_one_iff _ _).mp (h.1 i)).symm.trans ih

theorem unique_orientation (k : Nat) (f : Fin (k+1) → Bool) (h : Feasible k f) :
    ∃! b : Bool, f = fun _ => b := by
  refine ⟨f 0, ?_, ?_⟩
  · funext i
    exact word_constant k f h i
  · intro b hb
    exact (congrFun hb 0).symm


end R03OrientationWordsM6

open R03OrientationWordsM6
theorem solution (k : Nat) :
    Fintype.card {f : Fin (k+1) → Bool // Feasible k f} = 2 := by
  classical
  let e : {f : Fin (k+1) → Bool // Feasible k f} ≃ Bool := {
    toFun := fun f => f.val 0
    invFun := fun b => ⟨fun _ => b, by
      constructor
      · intro i
        cases b <;> rfl
      · cases b <;> rfl⟩
    left_inv := by
      intro f
      apply Subtype.ext
      funext i
      exact (word_constant k f.val f.property i).symm
    right_inv := by intro b; rfl }
  calc
    _ = Fintype.card Bool := Fintype.card_congr e
    _ = 2 := by decide

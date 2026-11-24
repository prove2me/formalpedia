-- Prove2me | solution 1 for PositivityTheory.ThKCT.Fr.cols_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:49:04.206342+00:00
-- url     : https://prove2.me/submissions/7b9fb2e5-413c-4e1a-b058-ea4537b0960d

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_ColsOfMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKCT PositivityTheory.ThKCT.Fr
open Matrix
variable {R S : Type} [CommRing R] [CommRing S] {d e : Type} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
variable {ε : R} {A' : Matrix (e ⊕ Fin 2) d R} {c : R →+* R} {J : Matrix d d R} {J₁ : Matrix e e R} {ι : Matrix d e R} {x y : d → R}
omit [DecidableEq d] [DecidableEq e]
namespace PositivityTheory.ThKCT.Fr
theorem _root_.solution {m : Matrix d d R} {g : Matrix e e R} {b : Matrix e (Fin 2) R} {a : Matrix (Fin 2) e R}
    {s : Matrix (Fin 2) (Fin 2) R} (h : m * fr ι x y = fr ι x y * fromBlocks g b a s) :
    m * ι = ι * g + of (fun i j => ![x i, y i] j) * a ∧
      m *ᵥ x = ι *ᵥ (fun j => b j 0) + s 0 0 • x + s 1 0 • y ∧ m *ᵥ y = ι *ᵥ (fun j => b j 1) + s 0 1 • x + s 1 1 • y := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have := congrFun (congrFun h i) (Sum.inl j)
    simp [fr, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at this ⊢ <;>
      linear_combination this
  · ext i
    have := congrFun (congrFun h i) (Sum.inr 0)
    simp [fr, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two] at this ⊢ <;>
      linear_combination this
  · ext i
    have := congrFun (congrFun h i) (Sum.inr 1)
    simp [fr, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two] at this ⊢ <;>
      linear_combination this
end PositivityTheory.ThKCT.Fr

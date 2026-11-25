-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_sum_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:04:28.323895+00:00
-- url     : https://prove2.me/submissions/3de33dfa-a95a-47d3-a89d-507f9072acac

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_sum_update_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Finset
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (D n : ℕ) (g : (Fin (D + 1) → ℕ) → ℝ) :
    ∑ b ∈ Finset.Nat.antidiagonalTuple (D + 1) (n + 1), g b =
      ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, g (Function.update a 0 (a 0 + 1)) +
      ∑ b ∈ (Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => b 0 = 0), g b := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Nat.antidiagonalTuple (D + 1) (n + 1))
    (fun b : Fin (D + 1) → ℕ => b 0 = 0)]
  have key : ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, g (Function.update a 0 (a 0 + 1)) =
      ∑ b ∈ (Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => ¬ b 0 = 0), g b := by
    apply Finset.sum_nbij' (fun a => Function.update a 0 (a 0 + 1)) (fun b => Function.update b 0 (b 0 - 1))
    · intro a ha
      have ha' := Finset.Nat.mem_antidiagonalTuple.mp ha
      rw [Fin.sum_univ_succ] at ha'
      refine Finset.mem_filter.mpr ⟨Finset.Nat.mem_antidiagonalTuple.mpr ?_, ?_⟩
      · rw [chiPAux_sum_update_zero]
        omega
      · simp [Function.update_apply]
    · intro b hb
      have h1 := Finset.Nat.mem_antidiagonalTuple.mp (Finset.mem_filter.mp hb).1
      have h2 : b 0 ≠ 0 := (Finset.mem_filter.mp hb).2
      rw [Fin.sum_univ_succ] at h1
      apply Finset.Nat.mem_antidiagonalTuple.mpr
      rw [chiPAux_sum_update_zero]
      omega
    · intro a _
      funext i
      by_cases hi : i = 0
      · subst hi
        simp [Function.update_apply]
      · simp [Function.update_apply, hi]
    · intro b hb
      have h2 : b 0 ≠ 0 := (Finset.mem_filter.mp hb).2
      funext i
      by_cases hi : i = 0
      · subst hi
        simp [Function.update_apply] <;> omega
      · simp [Function.update_apply, hi]
    · intro a _
      rfl
  linarith [key]
end ReciprocityTheory.GeometryOfNumbersTheory

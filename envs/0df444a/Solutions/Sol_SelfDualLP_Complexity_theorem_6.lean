-- Prove2me | solution 1 for SelfDualLP.Complexity.theorem_6
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-11-06T04:34:15.719083+00:00
-- url     : https://prove2.me/submissions/a8d13103-51c5-42fa-bfed-e3b4b703da96

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Complexity_HLP
import Definitions.Def_SelfDualLP_Complexity_Neighborhood
import Definitions.Def_SelfDualLP_Complexity_PCSequence
import Definitions.Def_SelfDualLP_Complexity_Termination
import Definitions.Def_SelfDualLP_Complexity_BitLength

open Matrix

namespace SDLPThm6Counter

open SelfDualLP.Complexity

/-- The counterexample data: `m = 0`, `n = 1`, `c = (1)`. -/
def A0 : Matrix (Fin 0) (Fin 1) ℤ := 0
def b0 : Fin 0 → ℤ := 0
def c0 : Fin 1 → ℤ := fun _ => 1

lemma castVec_c0 (j : Fin 1) : castVec c0 j = 1 := by simp [castVec, c0]

/-- The predictor line through the initial point. -/
def P (a : ℝ) : HLPPoint 0 1 := ⟨0, fun _ => 1 - a, 1, 1 - a, fun _ => 1, 1 - a⟩

lemma nbhd_P (a : ℝ) (ha : a < 1) :
    Nbhd (castMat A0) (castVec b0) (castVec c0) (1 / 2) (P a) := by
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  · funext i; exact i.elim0
  · funext j
    simp [P, cbar, castVec_c0, ones, Matrix.mulVec, dotProduct]
  · simp [P, zbar, castVec_c0, ones, dotProduct]; ring
  · simp [P, bbar, cbar, zbar, castVec_c0, ones, dotProduct]; ring
  · intro j; simp [P]; linarith
  · simp [P]
  · intro j; simp [P]
  · simp [P]; linarith
  · intro j; simp [P]; linarith
  · simp [P]
  · intro j; simp [P]
  · simp [P]; linarith
  · have hmu : mu (P a) = 1 - a := by
      simp [mu, gap, P, dotProduct]; ring
    have hdev : centralityDeviation (P a) = 0 := by
      unfold centralityDeviation; rw [hmu]; simp [P]
    rw [hdev, hmu]; linarith

lemma dir_values (d : HLPPoint 0 1)
    (hd : IsPCDirection (castMat A0) (castVec b0) (castVec c0) (initialPoint 0 1) d 0) :
    d.x 0 = -1 ∧ d.τ = 0 ∧ d.θ = -1 ∧ d.s 0 = 0 ∧ d.κ = -1 := by
  obtain ⟨⟨_, h2, h3, h4⟩, h5, h6⟩ := hd
  have h2' := congrFun h2 0
  have h5' := h5 0
  simp [cbar, castVec_c0, ones, Matrix.mulVec, dotProduct] at h2'
  simp [bbar, cbar, zbar, castVec_c0, ones, dotProduct] at h3 h4
  simp [initialPoint, ones, mu, gap, dotProduct] at h5' h6
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

lemma move_eq (d : HLPPoint 0 1)
    (hd : IsPCDirection (castMat A0) (castVec b0) (castVec c0) (initialPoint 0 1) d 0)
    (a : ℝ) : (initialPoint 0 1).move d a = P a := by
  obtain ⟨hx, hτ, hθ, hs, hκ⟩ := dir_values d hd
  simp only [HLPPoint.move, initialPoint, P, ones, HLPPoint.mk.injEq]
  refine ⟨Subsingleton.elim _ _, ?_, ?_, ?_, ?_, ?_⟩
  · funext j; fin_cases j; simp [hx, ones]; ring
  · simp [hτ]
  · simp [hθ]; ring
  · funext j; fin_cases j; simp [hs, ones]
  · simp [hκ]; ring

end SDLPThm6Counter

open SelfDualLP.Complexity SDLPThm6Counter in
theorem solution : ¬ (∃ C : ℝ, 0 < C ∧ ∀ (m n : ℕ), 1 ≤ n →
      ∀ (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (c : Fin n → ℤ),
        ∃ (k : ℕ) (z : ℕ → HLPPoint m n),
          IsPCSequence (castMat A) (castVec b) (castVec c) z k ∧
          (k : ℝ) ≤ C * Real.sqrt (n : ℝ) * (bitLength A b c : ℝ) ∧
          (∃ u, IsTerminationOutput (castMat A) (castVec b) (castVec c) (z k) u) ∧
          ∀ u, IsTerminationOutput (castMat A) (castVec b) (castVec c) (z k) u →
            StrictlySelfComplementary7 (castMat A) (castVec b) (castVec c) (rescaleOutput u)) := by
  rintro ⟨C, -, h⟩
  obtain ⟨k, z, ⟨hz0, hstep⟩, -, ⟨u, hu⟩, hall⟩ := h 0 1 le_rfl A0 b0 c0
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `k = 0`: the termination output at the initial point has `τ = κ = 0`.
    have key := hall u hu
    rw [hz0] at hu
    obtain ⟨-, -, hcase⟩ := hu
    have hσ : (0 : Fin 1) ∈ sigmaSet (initialPoint 0 1) := by
      simp [sigmaSet, initialPoint, ones]
    rcases hcase with ⟨-, hκ, -, ⟨-, -, h3, -⟩, -⟩ | ⟨hlt, -⟩
    · have hτ := h3 0 hσ
      simp [castVec_c0, Matrix.mulVec, dotProduct] at hτ
      have hpos := key.2.2.2
      simp [rescaleOutput, HLPPoint.smul, hτ, hκ] at hpos
    · simp [initialPoint] at hlt
  · -- `k ≥ 1`: the first predictor step has no attained maximal step length.
    obtain ⟨d, hd⟩ := hstep 0 hk
    rcases hd with ⟨-, hdir, α, hα, -⟩ | ⟨hodd, -⟩
    · rw [hz0] at hα hdir
      have hmem := hα.1
      simp only [Set.mem_ofPred_eq, move_eq d hdir] at hmem
      have hlt : α < 1 := by
        have := hmem.1.2.1 0
        simp [P] at this; linarith
      have hmem2 : (α + 1) / 2 ∈ {a : ℝ | Nbhd (castMat A0) (castVec b0) (castVec c0) (1 / 2)
          ((initialPoint 0 1).move d a)} := by
        simp only [Set.mem_ofPred_eq, move_eq d hdir]
        exact nbhd_P _ (by linarith)
      have := hα.2 hmem2
      linarith
    · exact hodd (by decide)

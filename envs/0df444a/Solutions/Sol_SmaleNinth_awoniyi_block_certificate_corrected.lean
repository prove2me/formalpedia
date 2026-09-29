-- Prove2me | solution 1 for SmaleNinth.awoniyi_block_certificate_corrected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-25T09:29:05.134947+00:00
-- url     : https://prove2.me/submissions/c5cd43ef-8c5e-4e01-9d9a-622345e0fdc9

import Definitions.Def_Polyhedron
import Mathlib.Tactic

open Matrix LinearOptimization

theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (xp xm : Fin n → ℝ) (s y : Fin m → ℝ)
    (hxp : ∀ j, 0 ≤ xp j)
    (hxm : ∀ j, 0 ≤ xm j)
    (hs : ∀ i, 0 ≤ s i)
    (hblock : A.mulVec xp - A.mulVec xm - s = b)
    (hy : ∀ i, 0 ≤ y i)
    (hyA : ∀ k, ∑ i, y i * A i k = 0)
    (hcomp : ∀ i, y i * s i = 0) :
    ∃ x : Fin n → ℝ,
      x ∈ polyhedron A b ∧
      (∀ i, 0 ≤ y i) ∧
      (∀ k, ∑ i, y i * A i k = 0) ∧
      (∀ i, y i * ((A.mulVec x) i - b i) = 0) := by
  have hAx : A.mulVec (xp - xm) = b + s := by
    rw [mulVec_sub]
    funext i
    have hi := congrFun hblock i
    simp only [Pi.sub_apply, Pi.add_apply] at hi ⊢
    linarith
  refine ⟨xp - xm, ?_, hy, hyA, ?_⟩
  · intro i
    change b i ≤ (A.mulVec (xp - xm)) i
    rw [hAx]
    simp only [Pi.add_apply]
    exact le_add_of_nonneg_right (hs i)
  · intro i
    have hi := congrFun hAx i
    rw [hi]
    change y i * (b i + s i - b i) = 0
    calc
      y i * (b i + s i - b i) = y i * s i := by ring
      _ = 0 := hcomp i

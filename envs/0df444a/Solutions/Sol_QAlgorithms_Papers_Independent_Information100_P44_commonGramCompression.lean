-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.commonGramCompression
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:41:11.159797+00:00
-- url     : https://prove2.me/submissions/ff330fef-d25d-449c-bbac-958db1d48c3c

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix
open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P44

attribute [local instance] Classical.propDecidable

/-- PDF p.21, VI B: all blocks are computed from one positive global Gram object. -/
theorem solution {h g : ℕ} (G : Mat h) (hG : G.PosSemidef)
    (R S : Matrix (Fin h) (Fin g) ℂ) (z : Fin h → ℂ)
    (hR : Function.Injective R.mulVec) (hS : Function.Injective S.mulVec) :
    let A := Rᴴ * G * R
    let B := Sᴴ * G * S
    let F := Rᴴ * G * S
    let D := (Rᴴ * G).mulVec z
    let E := (Sᴴ * G).mulVec z
    let c := ∑ i, conj (z i) * (G.mulVec z) i
    ladderGram A B F D E c = (gramSelector R S z)ᴴ * G * gramSelector R S z ∧
      (ladderGram A B F D E c).PosSemidef := by
  intro A B F D E c
  have hGs : ∀ k l, star (G k l) = G l k := fun k l => hG.isHermitian.apply l k
  have hGc : ∀ k l, starRingEnd ℂ (G k l) = G l k := fun k l => hG.isHermitian.apply l k
  have key : ladderGram A B F D E c = (gramSelector R S z)ᴴ * G * gramSelector R S z := by
    ext i j
    rcases i with i | i | i <;> rcases j with j | j | j <;>
      simp only [ladderGram, Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.conjTranspose_apply] <;>
      simp [A, B, F, D, E, c, ladderGram, gramSelector, augment, Matrix.mul_apply, Matrix.mulVec,
        dotProduct, Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum, star_sum, hGs,
        mul_assoc, mul_comm, mul_left_comm] <;>
      first | rfl | skip
    all_goals first
      | exact Finset.sum_comm
      | (show starRingEnd ℂ (∑ x, ∑ y, G y x * (z x * starRingEnd ℂ (S y j))) = _
         simp [map_sum, hGc, mul_comm, mul_left_comm, mul_assoc]
         try exact Finset.sum_comm)
  refine ⟨key, ?_⟩
  rw [key]
  exact hG.conjTranspose_mul_mul_same _

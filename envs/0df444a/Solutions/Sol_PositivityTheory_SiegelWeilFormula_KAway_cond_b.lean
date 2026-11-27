-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KAway.cond_b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:21:28.032244+00:00
-- url     : https://prove2.me/submissions/de65192f-684b-4d15-a79c-ccb498b9dffa

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_AwayActions_DecAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Matrix
open Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KAway
variable {R : Type} [CommRing R] {n : ℕ}
variable (c : R →+* R) (ε : ℤ)
namespace PositivityTheory.SiegelWeilFormula.KAway
theorem _root_.solution (hc : ∀ z, c (c z) = z) (A B D : Matrix (Fin n) (Fin n) R) (hA : IsUnit A.det) (h1 : Aᵀ * D.map c = 1)
    (h2 : Bᵀ * D.map c + (ε : R) • (Dᵀ * B.map c) = 0) : (A⁻¹ * B)ᵀ + (ε : R) • (A⁻¹ * B).map c = 0 := by
  have hinv : (A.map c)⁻¹ = (A⁻¹).map c := Matrix.inv_eq_left_inv (by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hA, Matrix.map_one c (map_zero c) (map_one c)])
  have hT : (Aᵀ)⁻¹ = D.map c := Matrix.inv_eq_right_inv h1
  have hcc : (D.map c).map c = D := by
    rw [Matrix.map_map]
    ext i j
    exact hc (D i j)
  have hD : Dᵀ * A.map c = 1 := by
    have h1' := congrArg (fun M : Matrix (Fin n) (Fin n) R => (M.map c)ᵀ) h1
    simp only [Matrix.map_mul, Matrix.transpose_map, hcc, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.map_one c (map_zero c) (map_one c), Matrix.transpose_one] at h1'
    exact h1'
  have hDi : (A.map c)⁻¹ = Dᵀ := Matrix.inv_eq_left_inv hD
  rw [Matrix.transpose_mul, Matrix.map_mul, Matrix.transpose_nonsing_inv, hT, ← hinv, hDi]
  exact h2
end PositivityTheory.SiegelWeilFormula.KAway

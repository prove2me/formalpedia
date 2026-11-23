-- Prove2me | solution 1 for P2M_GroupTheoreticShannonCapacity_MAlpha_M__principalSubmatrix_9b037532404d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:43:51.412881+00:00
-- url     : https://prove2.me/submissions/92be462b-3534-4c1a-b037-4d5e52afaa0c

import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MAlpha
open Matrix
namespace GroupTheoreticShannonCapacity.MAlpha
theorem _root_.solution (n : ℕ) (α : ℝ) (S : Finset (Fin n)) :
    P0Matrix.principalSubmatrix n (Mα n α) S = Mα S.card α := by
  ext i j
  simp only [P0Matrix.principalSubmatrix, Mα, Matrix.submatrix_apply, Matrix.of_apply]
  -- The embedding preserves order: i < j in Fin S.card iff f i < f j in Fin n
  let f := S.orderEmbOfFin rfl
  -- Use the fact that f is strictly monotone
  have hmono : StrictMono f := f.strictMono
  -- Case split on trichotomy
  rcases Nat.lt_trichotomy (i : ℕ) (j : ℕ) with hij_lt | hij_eq | hij_gt
  · -- i < j: both LHS and RHS are α
    have hfi_lt : ((S.orderEmbOfFin rfl) i : ℕ) < ((S.orderEmbOfFin rfl) j : ℕ) := hmono hij_lt
    simp only [hij_lt, hfi_lt, ↓reduceIte]
  · -- i = j: both are 0
    have heq : i = j := Fin.ext hij_eq
    subst heq
    simp only [lt_irrefl, ↓reduceIte]
  · -- i > j: both LHS and RHS are -1
    have hfi_gt : ((S.orderEmbOfFin rfl) i : ℕ) > ((S.orderEmbOfFin rfl) j : ℕ) := hmono hij_gt
    have hfi_not_lt : ¬(((S.orderEmbOfFin rfl) i : ℕ) < ((S.orderEmbOfFin rfl) j : ℕ)) :=
      Nat.not_lt.mpr (Nat.le_of_lt hfi_gt)
    have hij_not_lt : ¬((i : ℕ) < (j : ℕ)) := Nat.not_lt.mpr (Nat.le_of_lt hij_gt)
    simp only [hfi_not_lt, hij_not_lt, ↓reduceIte, hfi_gt, hij_gt]
end GroupTheoreticShannonCapacity.MAlpha

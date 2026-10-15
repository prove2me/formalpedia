-- Prove2me | solution 1 for ThreeSum.OneHotMask.eval_le
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:48:51.154684+00:00
-- url     : https://prove2.me/submissions/f0038cc8-b193-491b-9178-f8d34c941284

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.List.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# Evaluating a one-hot hash from a subset mask

The executable recursion examines exactly one bit per level using a cached
power of two.  Its result is the sum of the selected symbol coefficients,
and is connected here to the raw hashes used by the global encoding.
-/

namespace ThreeSum.OneHotMask

open Finset SubsetAddress LocalHashMoments
open scoped BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false







theorem eval_le_sourceProof {L m U : ℕ} {w0 w1 : ℕ → ℕ}
    (h0 : ∀ i < L, w0 i ≤ U) (h1 : ∀ i < L, w1 i ≤ U) :
    eval w0 w1 L m ≤ L*U := by
  induction L generalizing m with
  | zero => simp [eval]
  | succ L ih =>
    have h0L := h0 L (by omega)
    have h1L := h1 L (by omega)
    have h0' : ∀ i < L, w0 i ≤ U := fun i hi => h0 i (by omega)
    have h1' : ∀ i < L, w1 i ≤ U := fun i hi => h1 i (by omega)
    unfold eval
    split
    · have hh := ih (m := m) h0' h1'
      nlinarith
    · have hh := ih (m := m-2^L) h0' h1'
      nlinarith













































































end ThreeSum.OneHotMask

end


theorem solution : ∀ {L m U : Nat} {w0 w1 : Nat → Nat},
  (∀ (i : Nat), @LT.lt.{0} Nat instLTNat i L → @LE.le.{0} Nat instLENat (w0 i) U) →
    (∀ (i : Nat), @LT.lt.{0} Nat instLTNat i L → @LE.le.{0} Nat instLENat (w1 i) U) →
      @LE.le.{0} Nat instLENat (ThreeSum.OneHotMask.eval w0 w1 L m)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) L U) := by
  exact @ThreeSum.OneHotMask.eval_le_sourceProof

#print axioms solution

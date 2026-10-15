-- Prove2me | solution 1 for ThreeSum.BlockCoefficientRows.rows_flat
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:39:54.335867+00:00
-- url     : https://prove2.me/submissions/3534da2b-4a34-4c61-9a57-739739eaea11

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments

section


/-!
# Explicit row-major encoding of the block ground set

Block coordinates are numbered by `block * width + coordinate`. The
equivalence connects compact machine-mask tables on `Fin (J*L)` with the
sigma-typed block sets in the reporting proof. Flattened one-hot coefficients
already include their positional radix factors.
-/

namespace ThreeSum.BlockIndex

open Finset BlockRows BlockEncoding GlobalEncoding LocalHashMoments LocalCoverBounds
open scoped BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false




@[simp] theorem coordEquiv_val {J L : ℕ} (i : Fin J) (x : Fin L) :
    (coordEquiv J L ⟨i,x⟩).val = i.val*L+x.val := by
  simp [coordEquiv, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]















































































































end ThreeSum.BlockIndex

end

section


/-!
# Reading constructed block coefficients in the flat mask order

The imperative coefficient constructor writes rows. The mask evaluator reads
one flat array. These lemmas identify the two layouts, including empty ground
sets, and specialize them to the unchanged schedule-occurrence encoding.
-/

namespace ThreeSum.BlockCoefficientRows

open BlockRows BlockIndex BlockEncoding GlobalEncoding LocalCoverBounds






theorem rows_flat_sourceProof {μ : ℕ → ℤ} {dst0 dst1 J L p : ℕ}
    {sel : ℕ → ℕ} {w0 w1 : ℕ → ℕ → ℕ}
    (hrows : LightBlockCoefficients.Rows μ dst0 dst1 L p sel w0 w1 J) :
    (∀ i < J*L, μ (dst0+i) = (flat J L p sel w0 i : ℤ)) ∧
    (∀ i < J*L, μ (dst1+i) = (flat J L p sel w1 i : ℤ)) := by
  have read (dst : ℕ) (w : ℕ → ℕ → ℕ)
      (hr : ∀ a < J, ∀ x < L, μ (dst+a*L+x) = (p^a*w (sel a) x : ℤ)) :
      ∀ i < J*L, μ (dst+i) = (flat J L p sel w i : ℤ) := by
    intro i hi
    let c := (coordEquiv J L).symm ⟨i,hi⟩
    have hc : c.1.val*L+c.2.val = i := by
      rw [← coordEquiv_val]
      exact congrArg Fin.val ((coordEquiv J L).apply_symm_apply ⟨i,hi⟩)
    have hf : flat J L p sel w i = p^c.1.val*w (sel c.1.val) c.2.val := by
      simp only [flat,OneHotMask.extend,hi,dite_true]
      rfl
    rw [hf]
    simpa only [Nat.add_assoc,hc,Nat.cast_mul,Nat.cast_pow] using
      hr c.1.val c.1.isLt c.2.val c.2.isLt
  exact ⟨read dst0 w0 (fun a ha x hx => (hrows a ha x hx).1),
    read dst1 w1 (fun a ha x hx => (hrows a ha x hx).2)⟩






























































end ThreeSum.BlockCoefficientRows

end


theorem solution : ∀ {μ : Nat → Int} {dst0 dst1 J L p : Nat} {sel : Nat → Nat} {w0 w1 : Nat → Nat → Nat},
  ThreeSum.LightBlockCoefficients.Rows μ dst0 dst1 L p sel w0 w1 J →
    And
      (∀ (i : Nat),
        @LT.lt.{0} Nat instLTNat i (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J L) →
          @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst0 i))
            (@Nat.cast.{0} Int instNatCastInt (ThreeSum.BlockCoefficientRows.flat J L p sel w0 i)))
      (∀ (i : Nat),
        @LT.lt.{0} Nat instLTNat i (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J L) →
          @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst1 i))
            (@Nat.cast.{0} Int instNatCastInt (ThreeSum.BlockCoefficientRows.flat J L p sel w1 i))) := by
  exact @ThreeSum.BlockCoefficientRows.rows_flat_sourceProof

#print axioms solution

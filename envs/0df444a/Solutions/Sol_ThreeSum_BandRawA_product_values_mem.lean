-- Prove2me | solution 1 for ThreeSum.BandRawA.product_values_mem
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:04:44.143812+00:00
-- url     : https://prove2.me/submissions/9a716364-514b-4cb6-b3b7-a274e3578e0e

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
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
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
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
import Theorems.Thm_ThreeSum_BandRawA_mem_allProducts
import Theorems.Thm_ThreeSum_BandRawA_mem_row


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition

section


/-!
# Exact A-value incidences of the physical band-owner catalog

Each successful owner contributes only its A band. Labels retain the
physical owner slot and the coordinate in the retained sorted A array.
Equal values and equal triples in different owner slots remain distinct.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows BandEnumeration BandPartition

set_option maxHeartbeats 1600000
set_option maxRecDepth 7000









































































































theorem mem_firstRows {n g i : ℕ} {rs : List Record} {l : Label} :
    l ∈ firstRows n g rs i ↔
      l.owner < i ∧ l ∈ row n g l.owner (rs.getD l.owner default) := by
  constructor
  · intro hl
    obtain ⟨owner,ho,hl⟩ := List.mem_flatMap.mp hl
    have he := (mem_row.mp hl).2.1
    subst owner
    exact ⟨List.mem_range.mp ho,hl⟩
  · rintro ⟨ho,hl⟩
    exact List.mem_flatMap.mpr ⟨l.owner,List.mem_range.mpr ho,hl⟩

theorem position_lt {n g i : ℕ} {rs : List Record} {l : Label}
    (hl : l ∈ firstRows n g rs i) : l.position < n := by
  have hh := (mem_row.mp (mem_firstRows.mp hl).2).2.2.2
  exact hh.trans_le (stop_le n g _)











































end ThreeSum.BandRawA

end

section


/-!
# Physical incidence indices and their exact owner coordinates

An incidence at position `count owner + localA` retains that physical
owner and its sorted A coordinate. Every emitted index has exactly this
form, including equal values emitted by different owners.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows

set_option maxHeartbeats 1700000
set_option maxRecDepth 7000



































































theorem at_mem {n g k : ℕ} {rs : List Record}
    (hk : k < (items n g rs).length) : labelAt n g rs k ∈ items n g rs := by
  rw [labelAt,List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk



































theorem values_getD {n g k : ℕ} {rs : List Record} (f : ℕ → ℤ)
    (hk : k < (items n g rs).length) :
    (values f (items n g rs)).getD k 0=f (labelAt n g rs k).position := by
  unfold values labelAt
  rw [List.getD_map_of_lt _ hk default 0]


























end ThreeSum.BandRawA

end

section


/-!
# Exact original-value membership and equation coverage of the owner catalog

Normalized sorted coordinates remain distinct from original input
positions. The normalization membership equivalence transfers values back
to their original color classes; the color-class bridge can then recover
the required distinct original positions.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows BandEnumeration BandPartition Finset
open scoped BigOperators

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000







theorem product_values_mem_sourceProof {A B C : List ℤ} {g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ allProducts A.length B.length C.length g rs) :
    valueAt A.length g rs (fun i => A.getD i 0) t.1 ∈ A ∧
      B.getD t.2.1 0 ∈ B ∧ C.getD t.2.2 0 ∈ C := by
  obtain ⟨ha,hb,hc⟩ := mem_allProducts.mp ht
  have hap := position_lt (at_mem ha)
  have hbp := bandPositions_lt hb
  have hcp := bandPositions_lt hc
  refine ⟨?_,?_,?_⟩
  · rw [valueAt,values_getD _ ha,List.getD_eq_getElem _ _ hap]
    exact List.getElem_mem hap
  · rw [List.getD_eq_getElem _ _ hbp]
    exact List.getElem_mem hbp
  · rw [List.getD_eq_getElem _ _ hcp]
    exact List.getElem_mem hcp










































































end ThreeSum.BandRawA

end


theorem solution : ∀ {A B C : List.{0} Int} {g : Nat} {rs : List.{0} ThreeSum.BandCandidateRows.Record}
  {t : Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)},
  @Membership.mem.{0, 0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) (Finset.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)))
      (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)))
        (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))))
      (ThreeSum.BandRawA.allProducts (@List.length.{0} Int A) (@List.length.{0} Int B) (@List.length.{0} Int C) g rs)
      t →
    And
      (@Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) A
        (ThreeSum.BandRawA.valueAt (@List.length.{0} Int A) g rs
          (fun (i : Nat) => @List.getD.{0} Int A i (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat Nat) t)))
      (And
        (@Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) B
          (@List.getD.{0} Int B (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat Nat) t))
            (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) C
          (@List.getD.{0} Int C (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat Nat) t))
            (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  exact @ThreeSum.BandRawA.product_values_mem_sourceProof

#print axioms solution

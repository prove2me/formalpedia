-- Prove2me | solution 1 for ThreeSum.LightReportingPositiveMasks.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:11:20.453466+00:00
-- url     : https://prove2.me/submissions/835dae97-0018-40ab-8d30-6b00deed6f5a

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
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
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
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
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
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
import Theorems.Thm_ThreeSum_LightBlockChildrenIndexed_childPrefixes_length
import Theorems.Thm_ThreeSum_LightReportingGatherPair_program_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockMaskLayout
end ThreeSum.BlockMaskLayout
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockChildrenIndexed
end ThreeSum.LightBlockChildrenIndexed
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.ReportingHostPositive
end ThreeSum.ReportingHostPositive
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSumApsp
end ThreeSumApsp

section


/-!
# Segments of the memory

Seg μ a l says that the cells a, a + 1, …, a + l.length - 1 of the memory μ hold the list l.
SegN is Seg for a list of natural numbers, MatAt for a matrix written row by row, VecAt for a vector
of indices.  The file has the lemmas for reading a cell of a segment, writing into it, writing
elsewhere, and for cutting and joining segments.  Each of the four predicates has its lemma `keep`,
which carries it to a later memory.
-/

@[expose] public section

namespace Light

open ThreeSumApsp







variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}
































































































































/-- Reading a cell of a segment of natural numbers, with the proof that the index is in range. -/
theorem SegN.getElem {l : List ℕ} (h : SegN μ a l) {i : ℕ} (hi : i < l.length) :
    μ (a + i) = (l[i] : ℕ) := by
  rw [h i (by simpa using hi), List.getElem_map]































































end Light

end
end

section


/-! # The concrete child constructor extends the original valid reporting prefixes -/

namespace ThreeSum.LightBlockChildrenIndexed

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open BlockRows BlockIndex BlockMaskLayout BlockIndexedQuery BlockForced StoredReporting
open ReportingHostMasks QueryCoordinates GlobalEncoding LocalCoverBounds

variable {lim : Limits}








































































theorem childAt_eq_get {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hk : k < J) (i : ℕ) (hi : i < groupSize h) :
    childAt q pre hk i = (childPrefixes q pre hk)[i]'(by rw [childPrefixes_length]; exact hi) := by
  have hib : i < (childPrefixes q pre hk).length := by rw [childPrefixes_length]; exact hi
  simp only [childAt,List.getElem?_eq_getElem hib,Option.getD_some]


























































end ThreeSum.LightBlockChildrenIndexed

end

section


/-!
# Actual positive-query filtering for a reporting frontier

The scan writes exactly the indices of positive stored query counts, in input
order. Its cost is linear in the candidate count, and original input arrays
are preserved. It does not recompute or assume the query implementation.
-/

namespace ThreeSum.LightReportingFilter

open Light

variable {lim : Limits} {P : Program}


















@[simp] theorem mem_selected (count : ℕ → ℕ) (j i : ℕ) :
    i ∈ selected count j ↔ i < j ∧ 0 < count i := by
  simp [selected]
























































































end ThreeSum.LightReportingFilter

end

section


/-! # Actual gathered positive mask arrays are the exact original next-prefix list -/

namespace ThreeSum.LightReportingPositiveMasks

open Light Finset ThreeSum.SubsetAddress
open BlockRows BlockIndexedQuery BlockForced StoredReporting GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open LightBlockChildrenIndexed ReportingHostPositive

set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false

theorem ofFn_getD_map {α β : Type*} (xs : List α) (fallback : α) (f : α → β) :
    List.ofFn (fun i : Fin xs.length => f (xs[i.val]?.getD fallback)) = xs.map f := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  have hi'' : i < xs.length := by simpa only [List.length_map] using hi'
  simp only [List.getElem_ofFn,List.getElem_map,List.getElem?_eq_getElem hi'',Option.getD_some]

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]





theorem selected_index_lt {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k < J)
    {i : ℕ} (hi : i < (selectedIndices I w pre hk).length) :
    (selectedIndices I w pre hk)[i]?.getD 0 < groupSize h := by
  rw [List.getElem?_eq_getElem hi,Option.getD_some]
  exact (LightReportingFilter.mem_selected _ _ _).mp (List.getElem_mem hi) |>.1

theorem program_meets_sourceProof {μ : ℕ → ℤ} {h J k indices srcL srcR dstL dstR d : ℕ}
    (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (pre : List (Finset (Fin (512*h)))) (hk : k < J)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hindices : indices+(selectedIndices I w pre hk).length ≤ lim.space)
    (hsrcL : srcL+groupSize h ≤ lim.space) (hsrcR : srcR+groupSize h ≤ lim.space)
    (hdstL : dstL+(selectedIndices I w pre hk).length ≤ lim.space)
    (hdstR : dstR+(selectedIndices I w pre hk).length ≤ lim.space)
    (hsepIL : Apart indices (selectedIndices I w pre hk).length dstL (selectedIndices I w pre hk).length)
    (hsepIR : Apart indices (selectedIndices I w pre hk).length dstR (selectedIndices I w pre hk).length)
    (hsepLL : Apart srcL (groupSize h) dstL (selectedIndices I w pre hk).length)
    (hsepRL : Apart srcR (groupSize h) dstL (selectedIndices I w pre hk).length)
    (hsepRR : Apart srcR (groupSize h) dstR (selectedIndices I w pre hk).length)
    (hsepOut : Apart dstL (selectedIndices I w pre hk).length dstR (selectedIndices I w pre hk).length)
    (hreadI : SegN μ indices (selectedIndices I w pre hk))
    (hreadL : SegN μ srcL ((childPrefixes w.2.2 pre hk).map fun next =>
      subsetMask (leftPrefix (k+1) (prefixRows (J := J) next))))
    (hreadR : SegN μ srcR ((childPrefixes w.2.2 pre hk).map fun next =>
      subsetMask (rightPrefix (k+1) (outputRows w.2.2) (prefixRows (J := J) next))))
    (hword : ((2^(J*(512*h)+1) : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim LightReportingGatherPair.program 1 d
      [indices,srcL,srcR,(selectedIndices I w pre hk).length,groupSize h,dstL,dstR]
      μ (LightReportingGatherPair.time (selectedIndices I w pre hk).length)
      (fun _ ν =>
        SegN ν dstL ((positiveChildren I w pre hk).map fun next =>
          subsetMask (leftPrefix (k+1) (prefixRows (J := J) next))) ∧
        SegN ν dstR ((positiveChildren I w pre hk).map fun next =>
          subsetMask (rightPrefix (k+1) (outputRows w.2.2) (prefixRows (J := J) next))) ∧
        SameOutside2 μ ν dstL (selectedIndices I w pre hk).length dstR (selectedIndices I w pre hk).length) := by
  let index : ℕ → ℕ := fun i => (selectedIndices I w pre hk)[i]?.getD 0
  let left : ℕ → ℤ := fun i => (subsetMask (leftPrefix (k+1) (prefixRows (J := J) (childAt w.2.2 pre hk i))) : ℤ)
  let right : ℕ → ℤ := fun i => (subsetMask (rightPrefix (k+1) (outputRows w.2.2)
    (prefixRows (J := J) (childAt w.2.2 pre hk i))) : ℤ)
  have hI (i : ℕ) (hi : i < (selectedIndices I w pre hk).length) : μ (indices+i) = (index i : ℤ) := by
    have hh := hreadI.getElem hi
    simpa only [index,List.getElem?_eq_getElem hi,Option.getD_some] using hh
  have hL (i : ℕ) (hi : i < groupSize h) : μ (srcL+i) = left i := by
    unfold left
    rw [childAt_eq_get w.2.2 pre hk i hi]
    have hh := hreadL.getElem (i := i) (by simpa only [List.length_map,childPrefixes_length] using hi)
    simpa only [List.getElem_map] using hh
  have hR (i : ℕ) (hi : i < groupSize h) : μ (srcR+i) = right i := by
    unfold right
    rw [childAt_eq_get w.2.2 pre hk i hi]
    have hh := hreadR.getElem (i := i) (by simpa only [List.length_map,childPrefixes_length] using hi)
    simpa only [List.getElem_map] using hh
  have hmask (U : Finset (Fin (J*(512*h)))) : |(subsetMask U : ℤ)| ≤ lim.word := by
    rw [Int.abs_natCast]
    exact (Int.ofNat_le.mpr ((subsetMask_isMask U).1.le.trans
      (Nat.pow_le_pow_right (by decide) (by omega)))).trans hword
  have hh := LightReportingGatherPair.program_meets (d := d) (μ := μ) index left right
    hw hindices hsrcL hsrcR hdstL hdstR hsepIL hsepIR hsepLL hsepRL hsepRR hsepOut
    (fun i hi => selected_index_lt I w pre hk hi) hI hL hR
    (fun _ _ => hmask _) (fun _ _ => hmask _) hd
  have heL : List.ofFn (fun i : Fin (selectedIndices I w pre hk).length => left (index i.val)) =
      (((positiveChildren I w pre hk).map fun next => subsetMask
        (leftPrefix (k+1) (prefixRows (J := J) next))).map fun x : ℕ => (x : ℤ)) := by
    rw [ofFn_getD_map (selectedIndices I w pre hk) 0 left]
    simp only [positiveChildren,selectedIndices,List.map_map,left,Function.comp_def]
  have heR : List.ofFn (fun i : Fin (selectedIndices I w pre hk).length => right (index i.val)) =
      (((positiveChildren I w pre hk).map fun next => subsetMask
        (rightPrefix (k+1) (outputRows w.2.2) (prefixRows (J := J) next))).map fun x : ℕ => (x : ℤ)) := by
    rw [ofFn_getD_map (selectedIndices I w pre hk) 0 right]
    simp only [positiveChildren,selectedIndices,List.map_map,right,Function.comp_def]
  rw [heL,heR] at hh
  exact hh

end ThreeSum.LightReportingPositiveMasks

end

universe u_1 u_2 u_3

theorem solution : ∀ {lim : Light.Limits} {α : Type u_1} {β : Type u_2} {γ : Type u_3} [Fintype.{u_1} α] [Fintype.{u_2} β]
  [Fintype.{u_3} γ] [inst : DecidableEq.{u_1 + 1} α] [DecidableEq.{u_2 + 1} β] [DecidableEq.{u_3 + 1} γ] {μ : Nat → Int}
  {h J k indices srcL srcR dstL dstR d : Nat}
  (I : Finset.{max (max u_3 u_2) u_1} (ThreeSum.RawIncidences.RawItem.{u_1, u_2, u_3} h J α β γ))
  (w : ThreeSum.RawReporting.Wanted.{u_1} h J α)
  (pre :
    List.{0}
      (Finset.{0}
        (Fin
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
  (hk : @LT.lt.{0} Nat instLTNat k J),
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) indices
          (@List.length.{0} Nat
            (@ThreeSum.LightReportingPositiveMasks.selectedIndices.{u_1, u_2, u_3} α β γ inst h J k I w pre hk)))
        lim.space →
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcL (ThreeSum.LocalCoverBounds.groupSize h))
          lim.space →
        @LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcR
              (ThreeSum.LocalCoverBounds.groupSize h))
            lim.space →
          @LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dstL
                (@List.length.{0} Nat
                  (@ThreeSum.LightReportingPositiveMasks.selectedIndices.{u_1, u_2, u_3} α β γ inst h J k I w pre hk)))
              lim.space →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dstR
                  (@List.length.{0} Nat
                    (@ThreeSum.LightReportingPositiveMasks.selectedIndices.{u_1, u_2, u_3} α β γ inst h J k I w pre
                      hk)))
                lim.space →
              Light.Apart indices
                  (@List.length.{0} Nat
                    (@ThreeSum.LightReportingPositiveMasks.selectedIndices.{u_1, u_2, u_3} α β γ inst h J k I w pre hk))
                  dstL
                  (@List.length.{0} Nat
                    (@ThreeSum.LightReportingPositiveMasks.selectedIndices.{u_1, u_2, u_3} α β γ inst h J k I w pre
                      hk)) →
                Light.Apart indices
                    (@List.length.{0} Nat
                      (@ThreeSum.LightReportingPositiveMasks.selectedIndices.{u_1, u_2, u_3} α β γ inst h J k I w pre
                        hk))
                    dstR
                    (@List.length.{0} Nat
                      (@ThreeSum.LightReportingPositiveMasks.selectedIndices.{u_1, u_2, u_3} α β γ inst h J k I w pre
                        hk)) →
                  Light.Apart srcL (ThreeSum.LocalCoverBounds.groupSize h) dstL
                      (@List.length.{0} Nat
                        (@ThreeSum.LightReportingPositiveMasks.selectedIndices.{u_1, u_2, u_3} α β γ inst h J k I w pre
                          hk)) →
                    Light.Apart srcR (ThreeSum.LocalCoverBounds.groupSize h) dstL
                        (@List.length.{0} Nat
                          (@ThreeSum.LightReportingPositiveMasks.selectedIndices.{u_1, u_2, u_3} α β γ inst h J k I w
                            pre hk)) →
                      Light.Apart srcR (ThreeSum.LocalCoverBounds.groupSize h) dstR
                          (@List.length.{0} Nat
                            (@ThreeSum.LightReportingPositiveMasks.selectedIndices.{u_1, u_2, u_3} α β γ inst h J k I w
                              pre hk)) →
                        Light.Apart dstL
                            (@List.length.{0} Nat
                              (@ThreeSum.LightReportingPositiveMasks.selectedIndices.{u_1, u_2, u_3} α β γ inst h J k I
                                w pre hk))
                            dstR
                            (@List.length.{0} Nat
                              (@ThreeSum.LightReportingPositiveMasks.selectedIndices.{u_1, u_2, u_3} α β γ inst h J k I
                                w pre hk)) →
                          Light.SegN μ indices
                              (@ThreeSum.LightReportingPositiveMasks.selectedIndices.{u_1, u_2, u_3} α β γ inst h J k I
                                w pre hk) →
                            Light.SegN μ srcL
                                (@List.map.{0, 0}
                                  (List.{0}
                                    (Finset.{0}
                                      (Fin
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
                                  Nat
                                  (fun
                                      (next :
                                        List.{0}
                                          (Finset.{0}
                                            (Fin
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512)))
                                                h)))) =>
                                    @ThreeSum.SubsetAddress.subsetMask
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                                      (@ThreeSum.BlockIndexedQuery.leftPrefix J
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                        (@ThreeSum.StoredReporting.prefixRows J
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                          next)))
                                  (@ThreeSum.LightBlockChildrenIndexed.childPrefixes h J k
                                    (@Prod.snd.{0, 0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                      (ThreeSum.GlobalEncoding.GlobalOutput h J)
                                      (@Prod.snd.{u_1, 0} α
                                        (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                          (ThreeSum.GlobalEncoding.GlobalOutput h J))
                                        w))
                                    pre hk)) →
                              Light.SegN μ srcR
                                  (@List.map.{0, 0}
                                    (List.{0}
                                      (Finset.{0}
                                        (Fin
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
                                    Nat
                                    (fun
                                        (next :
                                          List.{0}
                                            (Finset.{0}
                                              (Fin
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512)))
                                                  h)))) =>
                                      @ThreeSum.SubsetAddress.subsetMask
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                                        (@ThreeSum.BlockIndexedQuery.rightPrefix J
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                          (@ThreeSum.BlockForced.outputRows h J
                                            (@Prod.snd.{0, 0}
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                              (ThreeSum.GlobalEncoding.GlobalOutput h J)
                                              (@Prod.snd.{u_1, 0} α
                                                (Prod.{0, 0}
                                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                  (ThreeSum.GlobalEncoding.GlobalOutput h J))
                                                w)))
                                          (@ThreeSum.StoredReporting.prefixRows J
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                            next)))
                                    (@ThreeSum.LightBlockChildrenIndexed.childPrefixes h J k
                                      (@Prod.snd.{0, 0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                        (ThreeSum.GlobalEncoding.GlobalOutput h J)
                                        (@Prod.snd.{u_1, 0} α
                                          (Prod.{0, 0}
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                            (ThreeSum.GlobalEncoding.GlobalOutput h J))
                                          w))
                                      pre hk)) →
                                @LE.le.{0} Int Int.instLEInt
                                    (@Nat.cast.{0} Int instNatCastInt
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                    lim.word →
                                  @LT.lt.{0} Nat instLTNat d lim.depth →
                                    Light.Meets lim ThreeSum.LightReportingGatherPair.program
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d
                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt indices)
                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcL)
                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcR)
                                            (@List.cons.{0} Int
                                              (@Nat.cast.{0} Int instNatCastInt
                                                (@List.length.{0} Nat
                                                  (@ThreeSum.LightReportingPositiveMasks.selectedIndices.{u_1, u_2, u_3}
                                                    α β γ inst h J k I w pre hk)))
                                              (@List.cons.{0} Int
                                                (@Nat.cast.{0} Int instNatCastInt
                                                  (ThreeSum.LocalCoverBounds.groupSize h))
                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dstL)
                                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dstR)
                                                    (@List.nil.{0} Int))))))))
                                      μ
                                      (ThreeSum.LightReportingGatherPair.time
                                        (@List.length.{0} Nat
                                          (@ThreeSum.LightReportingPositiveMasks.selectedIndices.{u_1, u_2, u_3} α β γ
                                            inst h J k I w pre hk)))
                                      fun (x : Int) (ν : Nat → Int) =>
                                      And
                                        (Light.SegN ν dstL
                                          (@List.map.{0, 0}
                                            (List.{0}
                                              (Finset.{0}
                                                (Fin
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512)))
                                                    h))))
                                            Nat
                                            (fun
                                                (next :
                                                  List.{0}
                                                    (Finset.{0}
                                                      (Fin
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                            (instOfNatNat (nat_lit 512)))
                                                          h)))) =>
                                              @ThreeSum.SubsetAddress.subsetMask
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512)))
                                                    h))
                                                (@ThreeSum.BlockIndexedQuery.leftPrefix J
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                  (@ThreeSum.StoredReporting.prefixRows J
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512)))
                                                      h)
                                                    next)))
                                            (@ThreeSum.ReportingHostPositive.positiveChildren.{u_1, u_2, u_3} α β γ inst
                                              h J k I w pre hk)))
                                        (And
                                          (Light.SegN ν dstR
                                            (@List.map.{0, 0}
                                              (List.{0}
                                                (Finset.{0}
                                                  (Fin
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512)))
                                                      h))))
                                              Nat
                                              (fun
                                                  (next :
                                                    List.{0}
                                                      (Finset.{0}
                                                        (Fin
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                              (instOfNatNat (nat_lit 512)))
                                                            h)))) =>
                                                @ThreeSum.SubsetAddress.subsetMask
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512)))
                                                      h))
                                                  (@ThreeSum.BlockIndexedQuery.rightPrefix J
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512)))
                                                      h)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                    (@ThreeSum.BlockForced.outputRows h J
                                                      (@Prod.snd.{0, 0}
                                                        (Fin
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                        (ThreeSum.GlobalEncoding.GlobalOutput h J)
                                                        (@Prod.snd.{u_1, 0} α
                                                          (Prod.{0, 0}
                                                            (Fin
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                (instOfNatNat (nat_lit 3))))
                                                            (ThreeSum.GlobalEncoding.GlobalOutput h J))
                                                          w)))
                                                    (@ThreeSum.StoredReporting.prefixRows J
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                          (instOfNatNat (nat_lit 512)))
                                                        h)
                                                      next)))
                                              (@ThreeSum.ReportingHostPositive.positiveChildren.{u_1, u_2, u_3} α β γ
                                                inst h J k I w pre hk)))
                                          (Light.SameOutside2 μ ν dstL
                                            (@List.length.{0} Nat
                                              (@ThreeSum.LightReportingPositiveMasks.selectedIndices.{u_1, u_2, u_3} α β
                                                γ inst h J k I w pre hk))
                                            dstR
                                            (@List.length.{0} Nat
                                              (@ThreeSum.LightReportingPositiveMasks.selectedIndices.{u_1, u_2, u_3} α β
                                                γ inst h J k I w pre hk)))) := by
  exact @ThreeSum.LightReportingPositiveMasks.program_meets_sourceProof

#print axioms solution

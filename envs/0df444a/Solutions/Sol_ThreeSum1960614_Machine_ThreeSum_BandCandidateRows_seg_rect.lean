-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.seg_rect
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:08:39.595761+00:00
-- url     : https://prove2.me/submissions/eeeec279-d0e7-4a7e-b2bf-d6e2d50dccf4

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LocalKeyArraySemantics_seg_flatMap_rows

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
namespace ThreeSum1960614.Machine.ThreeSum.BandEnumeration
end ThreeSum1960614.Machine.ThreeSum.BandEnumeration

namespace ThreeSum1960614.Machine

/-!
# The exact physical band-owner record order

There is one four-cell record for every owner-table cell, in BC, AB, AC
rectangle order. A zero flag is a lookup miss. Successful records retain
their physical owner slot even when several owners produce the same triple.
-/

namespace ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandCandidateRows


open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000



























theorem rect_length (m n : ℕ) (F : ℕ → ℕ → _root_.ThreeSum.BandCandidateRows.Record) : (_root_.ThreeSum.BandCandidateRows.rect m n F).length=m*n := by
  simp [_root_.ThreeSum.BandCandidateRows.rect,List.length_flatMap]







theorem rect_getD {m n i j : ℕ} (F : ℕ → ℕ → _root_.ThreeSum.BandCandidateRows.Record) (hi : i < m) (hj : j < n) :
    (_root_.ThreeSum.BandCandidateRows.rect m n F).getD (i*n+j) default=F i j := by
  have hi' : i < (List.range m).length := by simpa using hi
  have hj' : j < (List.range n).length := by simpa using hj
  rw [_root_.ThreeSum.BandCandidateRows.rect,_root_.ThreeSum.OutputDecodeOrder.getD_flatMap_uniform _ _ n (by simp) 0 default hi' hj]
  rw [List.getD_eq_getElem _ _ hi']
  simp only [List.getElem_range]
  rw [_root_.List.getD_map_of_lt _ hj' 0 default,List.getD_eq_getElem _ _ hj']
  simp only [List.getElem_range]



















end ThreeSum.BandCandidateRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # List and memory interfaces for the exact candidate record array -/

namespace ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandCandidateRows


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration

set_option maxHeartbeats 1300000











theorem seg_cells {μ : ℕ → ℤ} {dst : ℕ} (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (H : ∀ s < rs.length, _root_.ThreeSum1960614.Machine.Light.Seg μ (dst+4*s) (rs.getD s default).cells) :
    _root_.ThreeSum1960614.Machine.Light.Seg μ dst (_root_.ThreeSum.BandCandidateRows.cells rs) := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.LocalKeyArraySemantics.seg_flatMap_rows rs _root_.ThreeSum.BandCandidateRows.Record.cells 4 dst (by intro r _; rfl)
  intro s hs j hj
  have hrec := H s hs
  rw [List.getD_eq_getElem _ _ hs] at hrec
  have he := hrec j (by simpa [_root_.ThreeSum.BandCandidateRows.Record.cells] using hj)
  simpa only [Nat.mul_comm s 4,Nat.add_assoc] using he





end ThreeSum.BandCandidateRows

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration
set_option maxHeartbeats 1300000
section

theorem ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.seg_rect__implementation_f4a068f56f {μ : ℕ → ℤ} {dst m n : ℕ} (F : ℕ → ℕ → _root_.ThreeSum.BandCandidateRows.Record)
    (H : ∀ i < m, ∀ j < n, _root_.ThreeSum1960614.Machine.Light.Seg μ (dst+4*(i*n+j)) (F i j).cells) :
    _root_.ThreeSum1960614.Machine.Light.Seg μ dst (_root_.ThreeSum.BandCandidateRows.cells (_root_.ThreeSum.BandCandidateRows.rect m n F)) := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.seg_cells
  intro s hs
  have hs' : s < m*n := by rwa [_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.rect_length] at hs
  have hn : 0 < n := by
    by_contra h
    have hn : n=0 := by omega
    simp [hn] at hs'
  have hi : s/n < m := (Nat.div_lt_iff_lt_mul hn).mpr hs'
  have hj : s%n < n := Nat.mod_lt s hn
  have hindex : s/n*n+s%n=s := by simpa only [Nat.mul_comm] using Nat.div_add_mod s n
  have he := H (s/n) hi (s%n) hj
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.rect_getD F hi hj
  rw [hindex] at he hr
  rwa [hr]
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.seg_rect__implementation_f4a068f56f) := (@ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.seg_rect__implementation_f4a068f56f)

#print axioms solution

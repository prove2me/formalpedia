-- Prove2me | solution 1 for ThreeSum.LightSourceFinitePrepared.meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T17:56:52.99256+00:00
-- url     : https://prove2.me/submissions/fe214431-a538-4cb5-84ff-855f090cd576

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
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
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
import Mathlib.Algebra.Order.Ring.Nat
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
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Basic
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
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
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
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_LightCoverKeyData_Stored_of_kept
import Theorems.Thm_ThreeSum_LightSourceControlsHost_Procs_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.BlockSourceFlags
end ThreeSum.BlockSourceFlags
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverMetadata
end ThreeSum.LightLocalCoverMetadata
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
end ThreeSum.LightLocalCoverTables
namespace ThreeSum.LightResidueHistogram
end ThreeSum.LightResidueHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.SourceFiniteInputs
end ThreeSum.SourceFiniteInputs

section


/-!
# Proof rules for the light language

Ends lim P d s σ T Q says: the statement s, started in σ, ends within T steps in a state that
satisfies Q.  There is one rule for each construct; a rule turns a goal about a statement into goals
about its parts, so a proof follows the text of the program from top to bottom.  Recursion needs no
rule: a statement about a recursive procedure is proved by induction (in Lean) on a measure, and the
rule for calls unfolds the body.

There are three rules for loops: with an invariant indexed by the number of the round and a cost for
each round (Ends.while), the same with one cost for all rounds (Ends.whileConst), and, for a loop
whose number of rounds depends on the data, with a quantity that every round decreases
(Ends.whileVariant).

The file also has the basic facts about runs (a run stays a run when procedures are appended to the
program), notation for writing programs, the simplification set
`light_norm`, and the standing assumptions `Std` about the limits.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Runs -/



































/-! ## The rules -/






/-- More time and a weaker conclusion. -/
theorem Ends.mono {s σ T T' Q Q'} (h : Ends lim P d s σ T Q) (hT : T ≤ T')
    (hQ : ∀ σ', Q σ' → Q' σ') : Ends lim P d s σ T' Q' := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc.trans hT, hQ _ hq⟩



























































































































/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/




























/-! ## Simplification -/

attribute [simp] Expr.val Expr.cost Expr.Safe Op.eval Cond.Holds Cond.cost Cond.Safe frame
















/-! ## The limits -/
























end Light

end
end

section


/-!
# Calls

Meets lim P p d vals μ T R is the specification of a procedure: procedure number p of the program P,
run at depth d on the arguments vals in the memory μ, ends within T steps with a result and a memory
that satisfy R. A routine is proved to meet such a specification (Meets.of_body), and a caller uses
the specification only, so that the proof of a caller does not depend on the body of a callee.

The specification of a routine x, as its callers assume it, has the form
`∀ (data) μ, hypotheses → ∀ d, d + k ≤ lim.depth → Meets lim P p d vals μ T R`.  Here k is the
number of levels of calls that x needs below itself, and d, the depth at which the body of x runs,
comes last.

There is one rule for calls, in four forms.  It is told the fact about the callee, from which it
reads the values of the arguments, the time and what holds afterwards, and it asks for what follows
the call.  Three side goals have default proofs: the arguments are safe and have these values, one
more level of calls is allowed, and the time suffices.  Ends.callTo and Ends.callToThen are the rule
for a state ⟨frame l, μ⟩; Ends.callLast and Ends.callThen are the same for local variables that are
not given as a list.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Specifications of procedures -/







section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}








/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩

















end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : State → Prop} {s : Stmt}











































end

end Light

end
end

section


/-!
# A finite array minimum scan in the benchmark language

The selected index is a deterministic left-to-right minimum. Its value
can therefore instantiate the exact mean bound for offset balancing.
-/

namespace ThreeSum.LightMinimum

open Light





theorem least_lt (f : ℕ → ℤ) {n : ℕ} (hn : 0 < n) : least f n < n := by
  induction n with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero => simp [least]
      | succ n =>
          have h := ih (by omega)
          unfold least
          split <;> omega


































variable {lim : Limits} {P : Program} {d : ℕ}





































end ThreeSum.LightMinimum

end

section


/-!
# Exact semantic interfaces for constructed local-cover tables

The concrete matrix constructor uses the unchanged radix enumeration of
the original local maps. Its retained histograms and gathered coefficient
rows are identified with the original occurrence-indexed encoding.
-/

namespace ThreeSum.LightLocalCoverTables

open Light LocalHashMoments LocalCoverBounds GlobalEncoding LightLocalCoverSchedule






























theorem Data.counts_read {μ : ℕ → ℤ} {h maps hist0 hist1 matrixPtr : ℕ}
    (H : Data μ h maps hist0 hist1 matrixPtr) {j r : ℕ} (hj : j < rows h) (hr : r < localPrime h) :
    μ (hist0+j*localPrime h+r) = (LocalCoverMatrix.leftCount (candidate h j) h r : ℤ) ∧
    μ (hist1+j*localPrime h+r) = (LocalCoverMatrix.rightCount (candidate h j) h r : ℤ) :=
  (H j hj).2.1 r hr

























































end ThreeSum.LightLocalCoverTables

end

section


/-!
# Constructed local-cover output as source-encoding input

This adapter connects the actual cover builder's retained candidate tables
and gathered occurrence rows to the exact reads used by source preparation.
Occurrence order, repeated candidates, and both independent bucket tables
are preserved without further searching or histogram construction.
-/

namespace ThreeSum.BlockSourceCoverInput

open Light GlobalEncoding LocalCoverBounds BlockCoefficientRows BlockSourceFlags













theorem of_cover {μ : ℕ → ℤ} {h allMaps matrix maps candidates histL histR : ℕ}
    (H : LightLocalCoverTables.Data μ h allMaps histL histR matrix)
    (R : LightLocalCoverTables.ScheduleRows μ h maps)
    (I : ∀ s : Occurrence h,
      μ (candidates+s.val) = (LightLocalCoverSchedule.candidateAt h s : ℤ)) :
    Input μ h maps candidates histL histR := by
  refine ⟨I,?_,?_,?_,?_⟩
  · intro s hs t ht
    simpa only [Nat.mul_comm s (2*(512*h))] using (R s hs t ht).1
  · intro s hs t ht
    simpa only [Nat.mul_comm s (2*(512*h))] using (R s hs t ht).2
  · intro k hk r hr
    exact (H.counts_read hk hr).1
  · intro k hk r hr
    exact (H.counts_read hk hr).2

































end ThreeSum.BlockSourceCoverInput

end

section


/-!
# Literal global-output records behind the radix key array

Local records use the verified layer enumerator's order and retain every
schedule occurrence. Cartesian extension enumerates each original global
output once. Mapping to integers may introduce equal values; the key array
retains all of those separate incidences.
-/

namespace ThreeSum.GlobalKeyEnumeration

open GlobalEncoding LocalGraph LocalCoverBounds LocalHashMoments
open RadixKeyLists
open scoped BigOperators

set_option maxHeartbeats 1800000


































































































theorem globalKeys_length (h J : ℕ) :
    (globalKeys h J).length=scheduleSize h^J*outputCount (512*h) h^J := by
  rw [globalKeys_eq_map,List.length_map,globalRecords_length]































end ThreeSum.GlobalKeyEnumeration

end

section


/-!
# An actual minimum scan of the fast cyclic correlation

The returned offset obeys the exact mean bound for the supplied histograms.
The choice is made by a fixed program, not by an existential witness in the
proof. The histograms themselves are the procedure's array inputs.
-/

namespace ThreeSum.LightBalancedOffset

open Light Karatsuba CyclicFold LightKaratsuba Finset
open scoped BigOperators




theorem offset_lt {p : ℕ} [NeZero p] (F H : ZMod p → ℕ) : offset F H < p :=
  LightMinimum.least_lt _ (Nat.pos_of_ne_zero (NeZero.ne p))





















variable {lim : Limits} {P : Program} {d : ℕ}






































































end ThreeSum.LightBalancedOffset

end

section


/-! # Retained local-cover tables survive reuse of the returned free region -/

namespace ThreeSum.LightLocalCoverRetention

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMetadata

set_option maxHeartbeats 1000000






theorem table_ends_le (base h : ℕ) :
    maps base h+rows h*(2*(512*h)) ≤ nextFree base h ∧
    hist0 base h+rows h*localPrime h ≤ nextFree base h ∧
    hist1 base h+rows h*localPrime h ≤ nextFree base h ∧
    matrixPtr base h+rows h*cols h ≤ nextFree base h ∧
    candidates base h+scheduleSize h ≤ nextFree base h := by
  unfold nextFree scheduleMaps candidates work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr
    LightCoverGreedy.total LightCoverGreedy.out
  omega










































end ThreeSum.LightLocalCoverRetention

end

section


/-!
# The retained cover, output layers, and exact global key array

This bundle is produced by the actual cover/key host and remains valid when
later phases use its computed next free address. In particular the output
index decoder can read the original layer masks without reconstructing them.
-/

namespace ThreeSum.LightCoverKeyData

open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000




theorem global_length (h J : ℕ) : (globalKeys h J).length=LightGlobalKeys.localCount h^J := by
  simp only [globalKeys_length,LightGlobalKeys.localCount,mul_pow]

theorem layer_end_le_header (free h J : ℕ) :
    LightCoverKeys.afterCover free h+outputCount (512*h) h ≤ LightCoverKeys.keyHeader free h J := by
  unfold LightCoverKeys.keyHeader LightGlobalKeys.scratch
  omega

theorem afterCover_le_keyEnd (free h J : ℕ) : LightCoverKeys.afterCover free h ≤ keyEnd free h J := by
  have hh := layer_end_le_header free h J
  unfold keyEnd
  omega






















































end ThreeSum.LightCoverKeyData

end

section


/-!
# An actual common offset from two original signed key arrays

The fixed program builds both padded histograms, including reversal, from
the supplied integer keys. It computes its own power-of-two capacity and
chooses the least correlation minimum with the checked fast multiplication.
Repeated keys count separately. No histogram or capacity table is supplied.
-/

namespace ThreeSum.LightOriginalOffset

open Light LightResidues LightResidueHistogram
open KaratsubaInterface CyclicFold
open scoped BigOperators

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000





theorem selected_lt (p : ℕ) [NeZero p] (left right : ℕ → ℤ) (nLeft nRight : ℕ) :
    selected p left right nLeft nRight < p := LightBalancedOffset.offset_lt ..





























































variable {lim : Limits} {P : Program} {d : ℕ}








































































































































end ThreeSum.LightOriginalOffset

end

section


/-!
# Original A positions and all three guarded lifts

The physical key order is lift-major, preserving every original position.
The selected-offset count is transported to the unchanged guarded wanted
labels used by raw reporting, including repeated input values.
-/

namespace ThreeSum.RawAKeyLists

open GlobalEncoding RawIncidences GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open scoped BigOperators

set_option maxHeartbeats 900000






















theorem keys_length (P : ℤ) (xs : List ℤ) : (keys P xs).length=3*xs.length := by
  rw [keys,List.length_map,records_length]











































































































end ThreeSum.RawAKeyLists

end

section


/-!
# Actual cover construction, lifted A keys, and balanced wanted records

This closed program runs the local-cover initializer and global key product,
constructs all three lifts of the supplied A incidences, selects the common
offset, and emits precisely the matching position pairs. Every dimension and
output address is read or computed. The retained cover, layers and coefficient
tables are available to the source-bank and output-decoding phases afterwards.
-/

namespace ThreeSum.LightGuardedWanted

open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds

set_option maxHeartbeats 2400000
set_option maxRecDepth 10000








































theorem selected_eq (P M h J : ℕ) [NeZero M] (xs : List ℤ) :
    LightOriginalOffset.selected M (left P xs) (right h J) (3*xs.length) (totalKeys h J)=
      RawAKeyLists.selected M P xs h J := by
  unfold RawAKeyLists.selected GlobalKeyOffset.selected
  rw [RawAKeyLists.keys_length,LightCoverKeyData.global_length]
  rfl






















variable {lim : Limits}






















































































end ThreeSum.LightGuardedWanted

end

section


/-! # Concrete source inputs from the retained normalization and wanted outputs -/

namespace ThreeSum.SourceFiniteInputs

open Light GlobalEncoding LocalCoverBounds LightLocalCoverLayout LightLocalCoverSchedule






theorem cover_input {μ : ℕ → ℤ} {free h J : ℕ} (H : LightCoverKeyData.Stored μ free h J) :
    BlockSourceCoverInput.Input μ h (maps free h) (candidates free h) (leftCounts free h) (rightCounts free h) :=
  BlockSourceCoverInput.of_cover H.data H.rows H.indices

theorem cover_ends (free h J : ℕ) :
    maps free h+2*(512*h)*scheduleSize h ≤ LightCoverKeyData.keyEnd free h J ∧
    candidates free h+scheduleSize h ≤ LightCoverKeyData.keyEnd free h J ∧
    leftCounts free h+rows h*localPrime h ≤ LightCoverKeyData.keyEnd free h J ∧
    rightCounts free h+rows h*localPrime h ≤ LightCoverKeyData.keyEnd free h J := by
  have hh := LightCoverKeyData.afterCover_le_keyEnd free h J
  obtain ⟨_,hl,hr,_,hc⟩ := LightLocalCoverRetention.table_ends_le (LightLocalCoverInit.base free) h
  have hm : maps free h+2*(512*h)*scheduleSize h=LightCoverKeys.afterCover free h := by
    unfold maps LightCoverKeys.afterCover LightLocalCoverMetadata.nextFree
    rw [Nat.mul_comm (2*(512*h)) (scheduleSize h)]
  exact ⟨hm.le.trans hh,hc.trans hh,hl.trans hh,hr.trans hh⟩

theorem prepared_read {μ : ℕ → ℤ} {values endpoints g : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (H : LightBandPreprocessing.Represents μ values endpoints g hg original L hs) :
    ∀ j < L.length, μ (values+j)=L.getD j 0 := fun j hj => H.1.getD hj 0

theorem prepared_headers {μ : ℕ → ℤ} {values endpoints g : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (H : LightBandPreprocessing.Represents μ values endpoints g hg original L hs) :
    μ endpoints=(L.length : ℤ) ∧ μ (endpoints+1)=(BandPartition.size L.length g : ℤ) :=
  ⟨H.2.2.2.1,H.2.2.2.2.1⟩

theorem prepared_bound {μ : ℕ → ℤ} {values endpoints g U : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (H : LightBandPreprocessing.Represents μ values endpoints g hg original L hs)
    (hb : ∀ z ∈ original, |z| ≤ (U : ℤ)) :
    ∀ j < L.length, |L.getD j 0| ≤ (U : ℤ) := by
  intro j hj
  rw [List.getD_eq_getElem _ _ hj]
  exact hb _ ((H.2.2.1 _).mp (List.getElem_mem hj))

theorem selected_lt (M P h J : ℕ) [NeZero M] (xs : List ℤ) :
    RawAKeyLists.selected M P xs h J < M := by
  rw [← LightGuardedWanted.selected_eq]
  exact LightOriginalOffset.selected_lt ..

theorem selected_abs_le (M P h J : ℕ) [NeZero M] (xs : List ℤ) :
    |(RawAKeyLists.selected M P xs h J : ℤ)| ≤ (M : ℤ) := by
  simpa only [abs_of_nonneg (Int.natCast_nonneg _)] using
    (Int.ofNat_le.mpr (selected_lt M P h J xs).le)

theorem wanted_shift_read {μ : ℕ → ℤ} {free M P h J : ℕ} [NeZero M] {xs : List ℤ}
    (H : LightWantedSetup.Output μ (LightGuardedWanted.wantedFree free h J xs.length) M
      (LightGuardedWanted.left P xs) (LightGuardedWanted.right h J)
      (3*xs.length) (LightGuardedWanted.totalKeys h J) (RawAKeyLists.selected M P xs h J)) :
    μ (LightGuardedWanted.wantedFree free h J xs.length+3)=(RawAKeyLists.selected M P xs h J : ℤ) :=
  H.2.2.2.1

end ThreeSum.SourceFiniteInputs

end

section


/-! # Actual source construction from the retained prepared outputs -/

namespace ThreeSum.LightSourceFinitePrepared

open Light GlobalEncoding LocalCoverBounds BlockSourceEncoding SourceFiniteInputs






variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets_sourceProof {pMain : ℕ} (R : LightSourceControlsHost.Procs P pMain)
    {μ : ℕ → ℤ} {free base bv be cv ce g p h J cut U M : ℕ} [NeZero M]
    {hg : 0 < g} {originalB originalC B C xs : List ℤ}
    {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+16 ≤ lim.depth)
    (hp : 0 < p) (hcut : cut ≤ J*(512*h))
    (hbv : bv+originalB.length ≤ base) (hcv : cv+originalC.length ≤ base)
    (hbe : be+2 ≤ base) (hce : ce+2 ≤ base)
    (hshiftCell : LightGuardedWanted.wantedFree free h J xs.length+3 < base)
    (hspace : LightSourceControlsHost.space base B.length C.length g p h J cut U M ≤ lim.space)
    (hword : (LightSourceControlsHost.word B.length C.length g p h J cut U M : ℤ) ≤ lim.word)
    (hB : LightBandPreprocessing.Represents μ bv be g hg originalB B hsB)
    (hC : LightBandPreprocessing.Represents μ cv ce g hg originalC C hsC)
    (hboundB : ∀ z ∈ originalB, |z| ≤ (U : ℤ)) (hboundC : ∀ z ∈ originalC, |z| ≤ (U : ℤ))
    (hcover : LightCoverKeyData.Stored μ free h J)
    (hwanted : LightWantedSetup.Output μ (LightGuardedWanted.wantedFree free h J xs.length) M
      (LightGuardedWanted.left p xs) (LightGuardedWanted.right h J)
      (3*xs.length) (LightGuardedWanted.totalKeys h J) (RawAKeyLists.selected M p xs h J)) :
    Meets lim P pMain d (args free base bv be cv ce g p h J cut xs.length) μ
      (LightSourceControlsHost.time B.length C.length g p h J cut U M)
      (fun r ν => SourceFiniteData.Stored ν base g p h J cut B C
        (RawAKeyLists.selected M p xs h J : ℤ) r ∧ LightCoverKeyData.Stored ν free h J ∧ Kept μ ν base) := by
  have hkey : LightCoverKeyData.keyEnd free h J ≤ base := by
    unfold LightGuardedWanted.wantedFree at hshiftCell
    omega
  obtain ⟨hmaps,hcandidates,hleft,hright⟩ := cover_ends free h J
  obtain ⟨hlenB,hcountB⟩ := prepared_headers hB
  obtain ⟨hlenC,hcountC⟩ := prepared_headers hC
  have H := R.meets (μ := μ) (srcL := bv) (headL := be) (srcR := cv) (headR := ce)
    (shiftCell := LightGuardedWanted.wantedFree free h J xs.length+3) (base := base)
    (NL := B.length) (NR := C.length) (g := g) (p := p) (h := h) (J := J) (cut := cut) (U := U) (D := M)
    (maps := maps free h) (candidates := candidates free h) (histL := leftCounts free h) (histR := rightCounts free h)
    (shift := (RawAKeyLists.selected M p xs h J : ℤ)) (fun j => B.getD j 0) (fun j => C.getD j 0)
    hw hd hg hp hcut (by have hl := hB.2.1; omega) (by have hl := hC.2.1; omega)
    hbe hce hshiftCell (hmaps.trans hkey) (hcandidates.trans hkey) (hleft.trans hkey) (hright.trans hkey)
    hspace hword (selected_abs_le M p h J xs) hlenB hlenC hcountB hcountC
    (wanted_shift_read hwanted) (prepared_read hB) (prepared_read hC)
    (prepared_bound hB hboundB) (prepared_bound hC hboundC) (cover_input hcover)
  apply H.mono le_rfl
  intro r ν ⟨hr,hcontrols,hbuckets,hbanks,hkeep⟩
  exact ⟨⟨hr,hcontrols,hbuckets,hbanks⟩,hcover.of_kept (fun a ha => hkeep a (ha.trans_le hkey)),hkeep⟩

end ThreeSum.LightSourceFinitePrepared

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (R : ThreeSum.LightSourceControlsHost.Procs P pMain)
  {μ : Nat → Int} {free base bv be cv ce g p h J cut U M : Nat}
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
  {hg : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) g}
  {originalB originalC B C xs : List.{0} Int}
  {hsB : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) B}
  {hsC : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) C},
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
          (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))))
        lim.depth →
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p →
        @LE.le.{0} Nat instLENat cut
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)) →
          @LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bv (@List.length.{0} Int originalB))
              base →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cv (@List.length.{0} Int originalC))
                base →
              @LE.le.{0} Nat instLENat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) be
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  base →
                @LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ce
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    base →
                  @LT.lt.{0} Nat instLTNat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (ThreeSum.LightGuardedWanted.wantedFree free h J (@List.length.{0} Int xs))
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      base →
                    @LE.le.{0} Nat instLENat
                        (ThreeSum.LightSourceControlsHost.space base (@List.length.{0} Int B) (@List.length.{0} Int C) g
                          p h J cut U M)
                        lim.space →
                      @LE.le.{0} Int Int.instLEInt
                          (@Nat.cast.{0} Int instNatCastInt
                            (ThreeSum.LightSourceControlsHost.word (@List.length.{0} Int B) (@List.length.{0} Int C) g p
                              h J cut U M))
                          lim.word →
                        ThreeSum.LightBandPreprocessing.Represents μ bv be g hg originalB B hsB →
                          ThreeSum.LightBandPreprocessing.Represents μ cv ce g hg originalC C hsC →
                            (∀ (z : Int),
                                @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) originalB z →
                                  @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup z)
                                    (@Nat.cast.{0} Int instNatCastInt U)) →
                              (∀ (z : Int),
                                  @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) originalC z →
                                    @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup z)
                                      (@Nat.cast.{0} Int instNatCastInt U)) →
                                ThreeSum.LightCoverKeyData.Stored μ free h J →
                                  ThreeSum.LightWantedSetup.Output μ
                                      (ThreeSum.LightGuardedWanted.wantedFree free h J (@List.length.{0} Int xs)) M
                                      (ThreeSum.LightGuardedWanted.left p xs) (ThreeSum.LightGuardedWanted.right h J)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                        (@List.length.{0} Int xs))
                                      (ThreeSum.LightGuardedWanted.totalKeys h J)
                                      (@Nat.cast.{0} Int instNatCastInt
                                        (@ThreeSum.RawAKeyLists.selected M inst (@Nat.cast.{0} Int instNatCastInt p) xs
                                          h J)) →
                                    Light.Meets lim P pMain d
                                      (ThreeSum.LightSourceFinitePrepared.args free base bv be cv ce g p h J cut
                                        (@List.length.{0} Int xs))
                                      μ
                                      (ThreeSum.LightSourceControlsHost.time (@List.length.{0} Int B)
                                        (@List.length.{0} Int C) g p h J cut U M)
                                      fun (r : Int) (ν : Nat → Int) =>
                                      And
                                        (ThreeSum.SourceFiniteData.Stored ν base g p h J cut B C
                                          (@Nat.cast.{0} Int instNatCastInt
                                            (@ThreeSum.RawAKeyLists.selected M inst (@Nat.cast.{0} Int instNatCastInt p)
                                              xs h J))
                                          r)
                                        (And (ThreeSum.LightCoverKeyData.Stored ν free h J) (Light.Kept μ ν base)) := by
  exact @ThreeSum.LightSourceFinitePrepared.meets_sourceProof

#print axioms solution

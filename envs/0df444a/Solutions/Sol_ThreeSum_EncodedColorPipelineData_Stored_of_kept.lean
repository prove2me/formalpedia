-- Prove2me | solution 1 for ThreeSum.EncodedColorPipelineData.Stored.of_kept
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:06:41.183976+00:00
-- url     : https://prove2.me/submissions/82a0e9da-cad3-4cd1-8b7f-9489efa64925

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
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
import Definitions.Def_ThreeSum1962Source_Bundle16
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
import Theorems.Thm_ThreeSum_EncodedColorPipelineData_ordered
import Theorems.Thm_ThreeSum_EncodedColorPrimeData_Stored_of_kept
import Theorems.Thm_ThreeSum_LightCoverKeyData_Stored_of_kept
import Theorems.Thm_ThreeSum_SourceBandBankData_Stored_of_kept
import Theorems.Thm_ThreeSum_SourceBandPairData_Stored_of_kept
import Theorems.Thm_ThreeSum_SourceFiniteData_Normalized_keep


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.WantedResidueKeys
end ThreeSum.WantedResidueKeys
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































































/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]

























/-- A segment all of whose cells are kept. -/
theorem Seg.of_sameOn {K : ℕ → Prop} (h : Seg μ b l) (hs : SameOn K μ μ')
    (hK : ∀ i < l.length, K (b + i)) : Seg μ' b l := h.congr fun i hi => hs _ (hK i hi)





































































































end Light

end
end

section


/-!
# Original-input histograms give the exact independently trimmed sources

The histogram keys retain the first modular reduction and the signed carry
offset. Looking up the endpoint's final residue therefore counts precisely
the original divisibility condition in `BlockEncoding`. An explicit finite
enumeration accounts for every original input incidence once.
-/

namespace ThreeSum.BlockSourceEncoding

open Finset BlockEncoding GlobalEncoding LocalCoverBounds LightSourceResidues
open scoped BigOperators

set_option maxHeartbeats 1000000



































theorem modulus_pos (h J : ℕ) : 0 < modulus h J := pow_pos (localPrime_pos h) J




section OriginalSources

variable {β : Type*} [DecidableEq β]



























end OriginalSources

end ThreeSum.BlockSourceEncoding

end

section


/-!
# Stable extraction of one color class from the original signed array

The program reads stored colors and original values. It writes a length
header followed by exactly the selected values, optionally negated. Repeated
values are preserved; deduplication belongs to the later normalization pass.
-/

namespace ThreeSum.LightClassFilter

open Light

set_option maxHeartbeats 1200000












theorem items_length_le (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) :
    (items x color want scale n).length ≤ n := by
  simpa only [items,List.length_map,List.length_range] using
    List.length_filter_le (p := fun i => decide (color i = want)) (l := List.range n)

























variable {lim : Limits} {P : Program} {d : ℕ}























































































end ThreeSum.LightClassFilter

end

section


/-!
# Exact original-position semantics of the constructed color-class lists

The machine keeps repeated values within a class and negates the third
class. The list membership witnesses are original positions. Any binary
width large enough for the indices suffices for the deterministic family.
-/

namespace ThreeSum.ColorClassLists

open LightClassFilter




































theorem length_classList_le {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) : (classList p x c scale).length ≤ n :=
  items_length_le ..



































































end ThreeSum.ColorClassLists

end

section


/-!
# Problems, solvers, and the interpretation of "is solved in time T" in the light language

A *task* is a problem together with a calling convention: which arguments a procedure gets, what the
memory holds when it is called, and what the result and the memory have to be when it returns.
`Solves task P p T need` says that procedure number `p` of the program `P` solves the task within
`T` steps, if the limits of the run allow for `need`.  A reduction of the paper is a *host*: a
procedure that calls an arbitrary solver of another task.

Conventions.

* A solver gets sizes, a bound `U` on the absolute values of the numbers, the addresses of its
  arrays, and as last argument the free pointer `fr`.  All inputs and outputs lie below `fr`.  The
  solver may write its output segments and any cell from `fr` on, and no other cell.  Nothing is
  assumed about the cells from `fr` on, so a solver can be called again and again.
* A solver has to be correct for every valid bound `U` that it is given.
* A solver is a pair of a program and a procedure number.  What is proved about it holds for every
  program that begins with this program, so a host appends its own procedures.

A `Task` is a problem whose time and need depend on a size and a bound.  `TaskN` and `SolvesN` are
the same notions with a list of parameters.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

/-! ## Limits -/






























/-! ## Specifications of single routines -/

/-- A list below fr stays where it is if nothing below fr changes. -/
theorem Seg.of_kept {μ μ' : ℕ → ℤ} {a fr : ℕ} {l : List ℤ} (h : Seg μ a l) (hk : Kept μ μ' fr)
    (hle : a + l.length ≤ fr) : Seg μ' a l :=
  h.of_sameOn hk fun i hi => show a + i < fr by omega

/-! ## Tasks and solvers -/
























































































/-! ## Hosts -/






















/-! ## Tasks with a list of parameters -/














































end Light

end
end

section


/-! # One compact retained layout for a selected color -/

namespace ThreeSum.EncodedColorLayout





















theorem normalized_ends_before_count (free n g : ℕ) :
    av free n+n ≤ normalizedEnd free n g ∧ ae free n+2+2*n ≤ normalizedEnd free n g ∧
    bv free n+n ≤ normalizedEnd free n g ∧ be free n+2+2*n ≤ normalizedEnd free n g ∧
    cv free n+n ≤ normalizedEnd free n g ∧ ce free n+2+2*n ≤ normalizedEnd free n g ∧
    tables free n+ColorBandBounds.count n g ≤ normalizedEnd free n g ∧
    rec free n g+4*ColorBandBounds.count n g ≤ normalizedEnd free n g := by
  unfold normalizedEnd LightBandRawA.space LightBandRawA.positionBase LightBandRawA.ownerBase
    LightBandRawA.capacity vals rec tables ce cv be bv ae av
  omega





















theorem prime_le_cover (free n g M y : ℕ) : prime free n g+6 ≤ cover free n g M y := by
  unfold cover EncodedColorPrimeData.nextFree EncodedColorPrimeData.prefixBase EncodedColorPrimeData.poolBase
  omega

theorem normalized_ends_cover (free n g M y : ℕ) :
    av free n+n ≤ cover free n g M y ∧ ae free n+2+2*n ≤ cover free n g M y ∧
    bv free n+n ≤ cover free n g M y ∧ be free n+2+2*n ≤ cover free n g M y ∧
    cv free n+n ≤ cover free n g M y ∧ ce free n+2+2*n ≤ cover free n g M y ∧
    tables free n+ColorBandBounds.count n g ≤ cover free n g M y ∧
    rec free n g+4*ColorBandBounds.count n g ≤ cover free n g M y ∧
    LightBandRawA.space (vals free n g) (ColorBandBounds.count n g) g ≤ cover free n g M y := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := normalized_ends_before_count free n g
  have h := prime_le_cover free n g M y
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ normalizedEnd free n g ≤ _
  unfold prime at h
  omega

end ThreeSum.EncodedColorLayout

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


/-! # Two retained original-band catalogs and one shared empty histogram -/

namespace ThreeSum.SourceBandPairData

open Light BandPartition






theorem work_ge (base n g m : ℕ) : base ≤ SourceBandLayout.work base n g m := by
  unfold SourceBandLayout.work SourceBandLayout.hist SourceBandLayout.data
  omega

theorem ordered (base NL NR g m : ℕ) :
    leftBase base ≤ rightBase base NL g m ∧
    rightBase base NL g m ≤ zeroBase base NL NR g m ∧
    zeroBase base NL NR g m < next base NL NR g m := by
  exact ⟨work_ge _ _ _ _,work_ge _ _ _ _,by unfold next; omega⟩










































































end ThreeSum.SourceBandPairData

end

section


/-! # Exact reusable memory boundary after the actual wanted-pair output -/

namespace ThreeSum.EncodedColorWantedData

open Light WantedResidueKeys




theorem header_le_nextFree (out M : ℕ) (left right : ℕ → ℤ) (NL NR : ℕ) (shift : ℤ) :
    out+4 ≤ nextFree out M left right NL NR shift := by
  unfold nextFree LightWantedSetup.pairBase LightSourceBucketSetup.next LightWantedSetup.bucketBase
    LightWantedSetup.rightCodes LightWantedSetup.leftCodes
  omega





theorem of_kept {μ ν : ℕ → ℤ} {out M NL NR bound : ℕ} {left right : ℕ → ℤ} {shift : ℤ}
    (H : LightWantedSetup.Output μ out M left right NL NR shift)
    (K : Kept μ ν bound) (hb : nextFree out M left right NL NR shift ≤ bound) :
    LightWantedSetup.Output ν out M left right NL NR shift := by
  have hh := (header_le_nextFree out M left right NL NR shift).trans hb
  obtain ⟨hcount,hpair,hnext,hshift,ps,hlen,hnodup,hmem,hrows⟩ := H
  refine ⟨(K _ (by omega)).trans hcount,(K _ (by omega)).trans hpair,
    (K _ (by omega)).trans hnext,(K _ (by omega)).trans hshift,ps,hlen,hnodup,hmem,?_⟩
  apply hrows.of_kept K
  rw [WantedPairs.cells_length,hlen]
  exact hb

end ThreeSum.EncodedColorWantedData

end

section


/-! # Keep the complete finite source catalog below its exact returned end -/

namespace ThreeSum.SourceFiniteData

open Light

theorem source_ends (base NL NR g h J cut : ℕ) :
    base+3 ≤ LightSourceControlsHost.finish base NL NR g h J cut ∧
    SourceBandPairData.next (LightSourceControlsHost.sourceBase base) NL NR g
      (BlockSourceEncoding.modulus h J) ≤ LightSourceControlsHost.finish base NL NR g h J cut ∧
    LightSourceBandHost.bankHeader (LightSourceControlsHost.sourceBase base) NL NR g h J+5 ≤
      LightSourceControlsHost.finish base NL NR g h J cut := by
  have ho := SourceBandPairData.ordered (LightSourceControlsHost.sourceBase base)
    NL NR g (BlockSourceEncoding.modulus h J)
  unfold LightSourceControlsHost.finish LightSourceBandHost.finish SourceBandBankData.finish
    SourceBandBankLayout.baseAt SourceBandBankData.first LightSourceBandHost.bankHeader
    LightSourceBandHost.occurrenceBase LightSourceControlsHost.sourceBase
  unfold SourceBandPairData.leftBase LightSourceControlsHost.sourceBase at ho
  omega

theorem Stored.of_kept {μ ν : ℕ → ℤ} {base g p h J cut bound : ℕ} {B C : List ℤ} {shift r : ℤ}
    (H : Stored μ base g p h J cut B C shift r)
    (K : Kept μ ν bound)
    (hb : LightSourceControlsHost.finish base B.length C.length g h J cut ≤ bound) :
    Stored ν base g p h J cut B C shift r := by
  obtain ⟨hcontrol,hpair,_⟩ := source_ends base B.length C.length g h J cut
  refine ⟨H.returned,?_,?_,?_⟩
  · exact H.controls.of_kept K (by simpa [SourceControlLayout.values] using hcontrol.trans hb)
  · exact H.buckets.of_kept (BlockSourceEncoding.modulus_pos h J) K (hpair.trans hb)
  · exact H.banks.of_kept K le_rfl hb

end ThreeSum.SourceFiniteData

end

section


/-! # Keep the complete selected-color payload while later stages extend memory -/

namespace ThreeSum.EncodedColorPipelineData

open Light Scales BandScales ColorClassLists EncodedColorNormalizedData

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
























theorem Stored.of_kept_sourceProof {μ ν : ℕ → ℤ} {free n stop : ℕ} {color : Coloring.Parameter (inputBits n+1)}
    {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : Stored μ free n color x A B C hsA hsB hsC) (K : Kept μ ν stop)
    (hstop : finish free n A B C hsA hsB hsC+8 ≤ stop) :
    Stored ν free n color x A B C hsA hsB hsC := by
  obtain ⟨hprime,hfree,hcover,hwanted,hcontrol,hbank⟩ := ordered free n A B C hsA hsB hsC
  have hcoverStop : EncodedColorLayout.cover free n (bandSize n) (radix n) (primeWindow n) ≤ stop := by
    change coverBase free n ≤ stop
    omega
  obtain ⟨hav,hae,hbv,hbe,hcv,hce,htables,hrecords,hcatalog⟩ :=
    EncodedColorLayout.normalized_ends_cover free n (bandSize n) (radix n) (primeWindow n)
  have hkey : LightCoverKeyData.keyEnd (coverBase free n) (microHalf (inputBits n)) (blockCount (inputBits n)) ≤ stop := by
    have hh : wantedHeader free n (incidences n A B C hsA hsB hsC).length=
        LightCoverKeyData.keyEnd (coverBase free n) (microHalf (inputBits n)) (blockCount (inputBits n))+
          3*(incidences n A B C hsA hsB hsC).length := rfl
    omega
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact H.heads.of_kept K (by simpa [values,LightEncodedColorResult.values] using hstop)
  · exact H.normalizedHeads.of_kept K (by
      simpa [EncodedColorLayout.normalizedHeads] using (show free+8 ≤ stop by omega))
  · rw [K _ (by unfold EncodedColorLayout.prime at hprime; omega)]
    exact H.countCell
  · exact H.normalized.keep K (length_classList_le color x 0 1) (length_classList_le color x 1 1)
      (length_classList_le color x 2 (-1)) (hav.trans hcoverStop) (hae.trans hcoverStop)
      (hbv.trans hcoverStop) (hbe.trans hcoverStop) (hcv.trans hcoverStop) (hce.trans hcoverStop)
      (htables.trans hcoverStop) (hrecords.trans hcoverStop) (hcatalog.trans hcoverStop)
  · exact H.primes.of_kept K (by change coverBase free n ≤ stop; omega)
  · exact H.cover.of_kept (fun i hi => K i (hi.trans_le hkey))
  · exact EncodedColorWantedData.of_kept H.wanted K (by change controls free n A B C hsA hsB hsC ≤ stop; omega)
  · exact H.sources.of_kept K (by change finish free n A B C hsA hsB hsC ≤ stop; omega)
  · rw [K _ (by omega)]
    exact H.countBound
  · apply H.lifts.of_kept K
    rw [RawAKeyLists.keys_length]
    change wantedHeader free n (incidences n A B C hsA hsB hsC).length ≤ stop
    omega








end ThreeSum.EncodedColorPipelineData

end


theorem solution : ∀ {μ ν : Nat → Int} {free n stop : Nat}
  {color :
    ThreeSum.Coloring.Parameter
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.Scales.inputBits n)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))}
  {x : Fin n → Int} {A B C : List.{0} Int}
  {hsA : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) A}
  {hsB : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) B}
  {hsC : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) C},
  ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC →
    Light.Kept μ ν stop →
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC)
            (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
          stop →
        ThreeSum.EncodedColorPipelineData.Stored ν free n color x A B C hsA hsB hsC := by
  exact @ThreeSum.EncodedColorPipelineData.Stored.of_kept_sourceProof

#print axioms solution

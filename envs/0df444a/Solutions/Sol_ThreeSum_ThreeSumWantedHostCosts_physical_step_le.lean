-- Prove2me | solution 1 for ThreeSum.ThreeSumWantedHostCosts.physical_step_le
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:34:09.573828+00:00
-- url     : https://prove2.me/submissions/e3acf30d-bab0-4f2d-b3b7-e67c244fc360

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_ThreeSum1962Source_Bundle16
import Definitions.Def_ThreeSum1962Source_Bundle17
import Definitions.Def_ThreeSum1962Source_Bundle18
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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_BandRawA_mem_aIndices_iff_owner
import Theorems.Thm_ThreeSum_BandRawA_mem_row
import Theorems.Thm_ThreeSum_SharedTraversalCosts_actual_dispatch_step_le


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.ReportingHostWantedConsumerData
end ThreeSum.ReportingHostWantedConsumerData
namespace ThreeSum.ReportingHostWantedOriginal
end ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum.ReportingHostWantedPhysical
end ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedTraversalCosts
end ThreeSum.SharedTraversalCosts
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds

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

theorem at_bounds {n g k : ℕ} {rs : List Record}
    (hk : k < (items n g rs).length) :
    (labelAt n g rs k).owner < rs.length ∧
      (ownerRecord n g rs k).flag=1 ∧
      BandPartition.start g (ownerRecord n g rs k).a ≤ (labelAt n g rs k).position ∧
      (labelAt n g rs k).position < BandPartition.stop n g (ownerRecord n g rs k).a := by
  have hh := mem_firstRows.mp (at_mem hk)
  have hr := mem_row.mp hh.2
  exact ⟨hh.1,hr.1,hr.2.2.1,hr.2.2.2⟩
























































end ThreeSum.BandRawA

end

section


/-!
# Bounded finite index types for the same physical owner products

The A type is the complete flattened incidence array; B and C are the
retained sorted arrays. Coordinate transport is injective and preserves
both each owner's product and its exact weighted collision score.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000


























@[simp] theorem mem_finiteAIndices {n g s : ℕ} {rs : List Record}
    {i : Fin (items n g rs).length} :
    i ∈ finiteAIndices n g rs s ↔ i.val ∈ aIndices n g rs s := by
  simp only [finiteAIndices,mem_filter,mem_univ,true_and]


















theorem finiteAIndices_owner {n g s : ℕ} {rs : List Record}
    (hs : s < rs.length) {i : Fin (items n g rs).length} :
    i ∈ finiteAIndices n g rs s ↔ (labelAt n g rs i.val).owner=s := by
  rw [mem_finiteAIndices,mem_aIndices_iff_owner hs]
  simp only [i.isLt,true_and]

































































































end ThreeSum.BandRawA

end

section


/-!
# Actual emitted slots decide the complete physical owner domain

Each slot selects its own independently retained B/C bands. Its terminal
semantics is the exact finite owner fiber, while the cumulative guard uses
their disjoint global union. This connects the physical wanted array to
original-value terminal tests at every permitted partial reporting depth.
-/

namespace ThreeSum.ReportingHostWantedOriginal

open Finset Light BandRawA BandCandidateRows RawIncidences RawReporting
open GlobalEncoding ReportingHostWantedPhysical
open ReportingHostFrontierLayout

set_option maxHeartbeats 2300000
set_option maxRecDepth 12000





































theorem owner_lt {h J n g : ℕ} (rs : List Record) (w : Wanted h J (AType n g rs)) :
    owner rs w<rs.length := (at_bounds w.1.isLt).1

theorem mem_owner {h J n g : ℕ} (rs : List Record) (w : Wanted h J (AType n g rs)) :
    w.1∈finiteAIndices n g rs (owner rs w) :=
  (finiteAIndices_owner (owner_lt rs w)).mpr rfl


























































section Actual

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ} {n NB NC g free P h J : ℕ}
  {rs : List Record} {shift : ℤ}
  (H : LightWantedSetup.Output μ free (LocalCoverBounds.localPrime h^J)
    (LightGuardedWanted.left P (values fA (items n g rs))) (LightGuardedWanted.right h J)
    (3*(values fA (items n g rs)).length) (LightGuardedWanted.totalKeys h J) shift)
























end Actual

end ThreeSum.ReportingHostWantedOriginal

end

section


/-!
# The physical reporting catalogs use the certified traversal ledger

The switch in every retained catalog is the literal switch used by the
original finite ledger. This module connects the executed level and terminal
costs to those exact binomial terms, preserving the sum over levels.
-/

namespace ThreeSum.SharedTraversalCosts

open Finset Scales LocalCoverBounds LightBlockQuery ReportingHostLevelData
open StageBounds CostLedger
open scoped BigOperators

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000





theorem residual_eq (n k : ℕ) :
    residualSize (half n) (blocks n) k=Switch.residualSize n k := rfl





























theorem physical_catalog_scales (n report NB NC g s i j : ℕ) :
    CatalogScales n (SharedReportingBankAccess.levelCatalog report (half n) (blocks n) NB NC g s i j) := by
  intro k hk
  change SharedReportingBankLevels.switch (half n) (blocks n) k=Switch.actualSwitch n k
  unfold SharedReportingBankLevels.switch Switch.actualSwitch
  congr 1
  rw [← residual_eq]
  unfold SharedReportingBankLevels.residual residualSize
  ring




















































































open Filter Real Parameters
open scoped Topology

noncomputable section












































end
end ThreeSum.SharedTraversalCosts

end

section


/-! # The retained physical wanted record uses the certified per-slot ledger -/

namespace ThreeSum.ThreeSumWantedHostCosts

open Light Scales BandScales BandRawA RawReporting RawIncidences GlobalEncoding
open ReportingHostWantedOriginal ReportingHostWantedConsumerData SharedTraversalCosts

set_option maxHeartbeats 1800000
set_option maxRecDepth 14000

theorem physical_step_le_sourceProof {free n output old threshold : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (w : Label n A B C hsA hsB hsC)
    (hkey : globalModulus (half n) (blocks n) ∣
      valueAt A.length (bandSize n) (EncodedColorWantedConsumerData.records n A B C hsA hsB hsC)
        (fun j => A.getD j 0) w.1.val%(EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)+
      lift w.2.1*(EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)+
      ThreeSumReportingSetupData.shift n A B C hsA hsB hsC-globalKey w.2.2) :
    LightReportingWantedDispatch.time (ThreeSumWantedHostData.config free n A B C hsA hsB hsC)
      (SharedReportingBankResourceBounds.wantedDecodeV n)
      (recordTime free n A B C hsA hsB hsC w output old threshold)+300 ≤
      scaledOverhead n*CostLedger.queryTerms n 0+scalarOverhead 4800 n+
        if threshold<old+labelMass n A B C hsA hsB hsC w then 0 else
          labelMass n A B C hsA hsB hsC w*(scaledOverhead n*
            (CostLedger.microPartitions n*CostLedger.allQueryTerms n+StageBounds.terminalChoices n)) := by
  let rs := EncodedColorWantedConsumerData.records n A B C hsA hsB hsC
  let D := ReportingHostWantedRecordData.catalogs A.length B.length C.length (bandSize n)
    (ThreeSumWantedHostData.config free n A B C hsA hsB hsC).report (half n) (blocks n) rs w output
  have hD : CatalogScales n D := physical_catalog_scales n
    (ThreeSumWantedHostData.config free n A B C hsA hsB hsC).report B.length C.length (bandSize n)
    (OutputDecodeOccurrenceCode.code (scheduleSize (half n)) (OutputDecodeRecords.layerCount (half n))
      (blocks n) output)
    (ownerRecord A.length (bandSize n) rs w.1.val).b (ownerRecord A.length (bandSize n) rs w.1.val).c
  have hh := actual_dispatch_step_le
    (cfg := ThreeSumWantedHostData.config free n A B C hsA hsB hsC) rfl rfl
    (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
    (ThreeSumReportingSetupData.shift n A B C hsA hsB hsC)
    (finiteAIndices A.length (bandSize n) rs (owner rs w))
    (finiteBandPositions B.length (bandSize n) (ownerRecord A.length (bandSize n) rs w.1.val).b)
    (finiteBandPositions C.length (bandSize n) (ownerRecord A.length (bandSize n) rs w.1.val).c)
    (fun i => valueAt A.length (bandSize n) rs (fun j => A.getD j 0) i.val)
    (fun i => B.getD i.val 0) (fun i => C.getD i.val 0)
    (left rs (fun j => B.getD j 0) w) (right rs (fun j => C.getD j 0) w)
    (finiteBandEquiv B.length (bandSize n) (ownerRecord A.length (bandSize n) rs w.1.val).b)
    (finiteBandEquiv C.length (bandSize n) (ownerRecord A.length (bandSize n) rs w.1.val).c)
    (fun _ => rfl) (fun _ => rfl) w D hD ⟨mem_owner rs w,hkey⟩
    (old := old) (threshold := threshold)
  exact hh

end ThreeSum.ThreeSumWantedHostCosts

end


theorem solution : ∀ {free n output old threshold : Nat} {A B C : List.{0} Int}
  {hsA : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) A}
  {hsB : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) B}
  {hsC : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) C}
  (w : ThreeSum.ReportingHostWantedConsumerData.Label n A B C hsA hsB hsC),
  @Dvd.dvd.{0} Int Int.instDvd
      (ThreeSum.GlobalEncoding.globalModulus (ThreeSum.SharedTraversalCosts.half n)
        (ThreeSum.SharedTraversalCosts.blocks n))
      (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
            (@HMod.hMod.{0, 0, 0} Int Int Int (@instHMod.{0} Int Int.instMod)
              (ThreeSum.BandRawA.valueAt (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n)
                (ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC)
                (fun (j : Nat) => @List.getD.{0} Int A j (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
                (@Fin.val
                  (@List.length.{0} ThreeSum.BandRawA.Label
                    (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n)
                      (ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC)))
                  (@Prod.fst.{0, 0}
                    (ThreeSum.ReportingHostWantedOriginal.AType (@List.length.{0} Int A)
                      (ThreeSum.BandScales.bandSize n)
                      (ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC))
                    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                        (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
                    w)))
              (@Nat.cast.{0} Int instNatCastInt (ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)))
            (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
              (ThreeSum.RawIncidences.lift
                (@Prod.fst.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                    (ThreeSum.SharedReportingBankResourceBounds.blocks n))
                  (@Prod.snd.{0, 0}
                    (ThreeSum.ReportingHostWantedOriginal.AType (@List.length.{0} Int A)
                      (ThreeSum.BandScales.bandSize n)
                      (ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC))
                    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                        (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
                    w)))
              (@Nat.cast.{0} Int instNatCastInt (ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC))))
          (ThreeSum.ThreeSumReportingSetupData.shift n A B C hsA hsB hsC))
        (@ThreeSum.GlobalEncoding.globalKey (ThreeSum.SharedReportingBankResourceBounds.half n)
          (ThreeSum.SharedReportingBankResourceBounds.blocks n)
          (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
              (ThreeSum.SharedReportingBankResourceBounds.blocks n))
            (@Prod.snd.{0, 0}
              (ThreeSum.ReportingHostWantedOriginal.AType (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n)
                (ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC))
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                  (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
              w)))) →
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (ThreeSum.LightReportingWantedDispatch.time (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC)
          (ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n)
          (ThreeSum.ReportingHostWantedConsumerData.recordTime free n A B C hsA hsB hsC w output old threshold))
        (@OfNat.ofNat.{0} Nat (nat_lit 300) (instOfNatNat (nat_lit 300))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (ThreeSum.SharedTraversalCosts.scaledOverhead n)
            (ThreeSum.CostLedger.queryTerms n (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (ThreeSum.SharedTraversalCosts.scalarOverhead
            (@OfNat.ofNat.{0} Nat (nat_lit 4800) (instOfNatNat (nat_lit 4800))) n))
        (@ite.{1} Nat
          (@LT.lt.{0} Nat instLTNat threshold
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
              (ThreeSum.ReportingHostWantedConsumerData.labelMass n A B C hsA hsB hsC w)))
          (threshold.decLt
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
              (ThreeSum.ReportingHostWantedConsumerData.labelMass n A B C hsA hsB hsC w)))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (ThreeSum.ReportingHostWantedConsumerData.labelMass n A B C hsA hsB hsC w)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (ThreeSum.SharedTraversalCosts.scaledOverhead n)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.CostLedger.microPartitions n)
                  (ThreeSum.CostLedger.allQueryTerms n))
                (ThreeSum.StageBounds.terminalChoices n)))))) := by
  exact @ThreeSum.ThreeSumWantedHostCosts.physical_step_le_sourceProof

#print axioms solution

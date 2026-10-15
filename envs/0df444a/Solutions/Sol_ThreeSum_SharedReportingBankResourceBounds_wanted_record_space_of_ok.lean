-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.wanted_record_space_of_ok
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:19:15.309643+00:00
-- url     : https://prove2.me/submissions/45cf5214-8a49-4195-b65b-95ba374ddd4d

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle16
import Definitions.Def_ThreeSum1962Source_Bundle17
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
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_buffers
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_numeric_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_record_scalars_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_scratch_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_work_le


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostSourceSelection
end ThreeSum.ReportingHostSourceSelection
namespace ThreeSum.ReportingHostSourceSelectionStored
end ThreeSum.ReportingHostSourceSelectionStored
namespace ThreeSum.ReportingHostWantedControls
end ThreeSum.ReportingHostWantedControls
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds

section


/-!
# Relative resources for the complete guarded wanted reporter

All buffer extents are relative to the caller's arbitrary free address.
Retained pointers are bounded individually by that address; they are never
summed into a purported size-only bound. Reserving frontier capacity does
not change the separately verified running time.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostWantedLayout ReportingHostFrontierLayout

set_option maxHeartbeats 2600000
set_option maxRecDepth 14000
set_option linter.unusedSectionVars false




















theorem wanted_work_eq (dst h J K N NB NC : ℕ) :
    (LightReportingWantedLayout.layout dst h J K N NB NC).work=
      dst+wantedWork h J K N NB NC := by
  unfold wantedWork LightReportingWantedLayout.layout make slot
    ReportingHostWantedLayout.root packed access decoded
  ring

theorem wanted_work_formula (h J K N NB NC : ℕ) :
    wantedWork h J K N NB NC=44+3*J+
      (K+1)*(4+2*capacityBound N NB NC (representationCap h J) (groupSize h))+
      5*groupSize h+12*2^(LightBlockQuery.width h J)+5*LightBlockQuery.width h J := by
  unfold wantedWork LightReportingWantedLayout.layout make slot
    ReportingHostWantedLayout.root packed access decoded
  ring


































































section Raw

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]







































end Raw
end ThreeSum.SharedReportingBankResourceBounds

end

section


/-! # Polynomial relative resources for every physical wanted slot -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Scales StageBounds GlobalEncoding LocalCoverBounds
open SharedReportingBankLayout ReportingHostWantedLayout

set_option maxHeartbeats 3200000
set_option maxRecDepth 16000




























































































theorem wanted_cells_le {n K N NB NC : ℕ}
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    wantedCells (half n) (blocks n) K N NB NC (wantedDecodeV n)≤wantedEnvelope n := by
  have hw := wanted_work_le hK hN hB hC
  have hn := wanted_numeric_le hK hN hB hC
  have hs := wanted_scratch_le n
  have h9 : (magnitude n+1)^9≤(magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h7 : (magnitude n+1)^7≤(magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h2 : (magnitude n+1)^2≤(magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  unfold wantedCells wantedEnvelope
  omega













































noncomputable section













theorem wanted_buffers_of_ok {lim : Limits} {dst n U K N NB NC d : ℕ}
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hok : (wantedNeed n U).Ok lim dst d) :
    WantedBuffers lim dst (half n) (blocks n) K N NB NC (wantedDecodeV n) :=
  wanted_buffers ((Nat.add_le_add_left (wanted_cells_le hK hN hB hC) dst).trans hok.cells)























end
end ThreeSum.SharedReportingBankResourceBounds

end

section


/-! # Individual selector bounds from the proved wanted Need -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light GlobalEncoding LocalCoverBounds ReportingHostWantedLayout
open ReportingHostSourceSelection ReportingHostSourceSelectionStored

set_option maxHeartbeats 2300000
set_option maxRecDepth 14000








































theorem wanted_access_output_le {lim : Limits} {dst n U K N NB NC d : ℕ}
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hok : (wantedNeed n U).Ok lim dst d) :
    ReportingHostWantedLayout.access dst (blocks n)+20≤lim.space := by
  have H := wanted_buffers_of_ok hK hN hB hC hok
  have hw := H.numeric
  have he := wanted_work_eq dst (half n) (blocks n) K N NB NC
  have hf := wanted_work_formula (half n) (blocks n) K N NB NC
  unfold ReportingHostWantedLayout.access decoded
  omega


































end ThreeSum.SharedReportingBankResourceBounds

end

section


/-! # Relative resources for the actual packed wanted-record call -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light GlobalEncoding LocalCoverBounds ReportingHostWantedLayout
open ReportingHostWantedControls

set_option maxHeartbeats 2100000
set_option maxRecDepth 16000

theorem wanted_record_space_of_ok_sourceProof {lim : Limits} {dst cover counter n U K N NB NC d : ℕ}
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hcover : cover+8≤dst) (hcounter : counter+2≤dst)
    (hok : (wantedNeed n U).Ok lim dst d) :
    LightReportingWantedRecordCall.space (access dst (blocks n)) dst cover counter
      (half n) (blocks n) K≤lim.space := by
  have H := wanted_buffers_of_ok hK hN hB hC hok
  have ha := wanted_access_output_le hK hN hB hC hok
  have hw := H.numeric
  have he := wanted_work_eq dst (half n) (blocks n) K N NB NC
  have hf := wanted_work_formula (half n) (blocks n) K N NB NC
  have hcell := hok.cells
  change dst+wantedEnvelope n≤lim.space at hcell
  have hn : LightReportingWantedRecordCall.numericExtra (half n) (blocks n) K≤lim.space :=
    (wanted_record_scalars_le hK).trans (by omega)
  unfold LightReportingWantedRecordCall.space
  apply max_le
  · exact max_le ha (by omega)
  · exact max_le (max_le (by omega) (by omega)) hn
























end ThreeSum.SharedReportingBankResourceBounds

end


theorem solution : ∀ {lim : Light.Limits} {dst cover counter n U K N NB NC d : Nat},
  @LE.le.{0} Nat instLENat K (ThreeSum.SharedReportingBankResourceBounds.blocks n) →
    @LE.le.{0} Nat instLENat N
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (ThreeSum.SharedReportingBankResourceBounds.magnitude n)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) →
      @LE.le.{0} Nat instLENat NB n →
        @LE.le.{0} Nat instLENat NC n →
          @LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cover
                (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
              dst →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) counter
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                dst →
              (ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst d →
                @LE.le.{0} Nat instLENat
                  (ThreeSum.LightReportingWantedRecordCall.space
                    (ThreeSum.ReportingHostWantedLayout.access dst
                      (ThreeSum.SharedReportingBankResourceBounds.blocks n))
                    dst cover counter (ThreeSum.SharedReportingBankResourceBounds.half n)
                    (ThreeSum.SharedReportingBankResourceBounds.blocks n) K)
                  lim.space := by
  exact @ThreeSum.SharedReportingBankResourceBounds.wanted_record_space_of_ok_sourceProof

#print axioms solution

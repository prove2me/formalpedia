-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.wanted_work_le
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:09:27.018492+00:00
-- url     : https://prove2.me/submissions/fc7fe2de-9ae9-4c81-8f22-d536b55afb73

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
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
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_components
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_representation_cap_le


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
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
# Size-only magnitudes for physical wanted indices

The left index includes the lift and the retained A-incidence position.
The right index selects an original output record, including its occurrence
identity. Neither bound depends on the magnitude of the input integers.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Scales GlobalEncoding LocalCoverBounds OutputDecodeRecords
open SharedReportingBankLayout

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000



theorem input_le_magnitude (n : ℕ) : n ≤ magnitude n := by
  have hn : n ≤ 2^(inputBits n+1) := by
    simpa only [inputBits,Nat.log2_eq_log_two,Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by decide : 1<2) n).le
  exact hn.trans (Nat.pow_le_pow_right (by decide) (by omega))




























































































end ThreeSum.SharedReportingBankResourceBounds

end

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


/-! # Explicit finite scale bounds for reporter words and the dense counter -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Scales Light GlobalEncoding LocalCoverBounds SharedReportingBankLayout
open ReportingHostWantedLayout

set_option maxHeartbeats 2800000
set_option maxRecDepth 14000




















theorem wanted_group_le_magnitude (n : ℕ) : groupSize (half n)≤magnitude n := by
  have hc : groupSize (half n)≤2^(2*half n) := Nat.choose_le_two_pow _ _
  exact hc.trans ((Nat.pow_le_pow_right (by decide) (by omega)).trans (components n).localPower)









































































theorem wanted_mass_bound_le {n N NB NC : ℕ}
    (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    massBound N NB NC (representationCap (half n) (blocks n))≤3*(magnitude n)^7 := by
  have hb := hB.trans (input_le_magnitude n)
  have hc := hC.trans (input_le_magnitude n)
  have hh := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hN hb) hc)
    (wanted_representation_cap_le n)
  calc
    _ ≤ ((3*(magnitude n)^3)*magnitude n)*magnitude n*(magnitude n)^2 := hh
    _ = _ := by ring



























end ThreeSum.SharedReportingBankResourceBounds

end

section


/-! # Polynomial relative resources for every physical wanted slot -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Scales StageBounds GlobalEncoding LocalCoverBounds
open SharedReportingBankLayout ReportingHostWantedLayout

set_option maxHeartbeats 3200000
set_option maxRecDepth 16000






theorem wanted_power_le (n e f : ℕ) (hef : e≤f) :
    (magnitude n)^e≤(magnitude n+1)^f :=
  (Nat.pow_le_pow_left (Nat.le_succ _) e).trans (Nat.pow_le_pow_right (by omega) hef)

theorem wanted_work_le_sourceProof {n K N NB NC : ℕ}
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    wantedWork (half n) (blocks n) K N NB NC≤100*(magnitude n+1)^9 := by
  have H := components n
  have hG := wanted_group_le_magnitude n
  have hJ := H.blocksBound
  have hW := H.widthBound
  have hT : 2^(width (half n) (blocks n))≤magnitude n :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans H.widthPower
  have hmass := wanted_mass_bound_le hN hB hC
  have hM7 := wanted_power_le n 7 7 le_rfl
  have h17 : 1≤(magnitude n+1)^7 := Nat.one_le_pow _ _ (by omega)
  have hmass' : massBound N NB NC (representationCap (half n) (blocks n))+1≤4*(magnitude n+1)^7 := by omega
  have hcap : capacityBound N NB NC (representationCap (half n) (blocks n)) (groupSize (half n))≤
      4*(magnitude n+1)^8 := by
    calc
      _ ≤ (4*(magnitude n+1)^7)*(magnitude n+1) :=
        Nat.mul_le_mul hmass' (hG.trans (Nat.le_succ _))
      _ = _ := by ring
  have h18 : 1≤(magnitude n+1)^8 := Nat.one_le_pow _ _ (by omega)
  have hstep : 4+2*capacityBound N NB NC (representationCap (half n) (blocks n)) (groupSize (half n))≤
      12*(magnitude n+1)^8 := by omega
  have hslot : (K+1)*(4+2*capacityBound N NB NC (representationCap (half n) (blocks n)) (groupSize (half n)))≤
      12*(magnitude n+1)^9 := by
    calc
      _ ≤ (magnitude n+1)*(12*(magnitude n+1)^8) :=
        Nat.mul_le_mul (by omega) hstep
      _ = _ := by ring
  have hM : magnitude n≤(magnitude n+1)^9 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  have h1 : 1≤(magnitude n+1)^9 := Nat.one_le_pow _ _ (by omega)
  rw [wanted_work_formula]
  dsimp only [width,localWidth,LightBlockQuery.width] at hW hT ⊢
  omega








































































































noncomputable section









































end
end ThreeSum.SharedReportingBankResourceBounds

end


theorem solution : ∀ {n K N NB NC : Nat},
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
            (ThreeSum.SharedReportingBankResourceBounds.wantedWork (ThreeSum.SharedReportingBankResourceBounds.half n)
              (ThreeSum.SharedReportingBankResourceBounds.blocks n) K N NB NC)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100)))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ThreeSum.SharedReportingBankResourceBounds.magnitude n)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))) := by
  exact @ThreeSum.SharedReportingBankResourceBounds.wanted_work_le_sourceProof

#print axioms solution

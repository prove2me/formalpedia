-- Prove2me | solution 1 for ThreeSum.SharedTraversalCosts.actual_dispatch_step_le
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:30:11.148509+00:00
-- url     : https://prove2.me/submissions/5c6fe6d4-9ba5-42ce-a3b2-626b6f25a400

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
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
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
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_candidates_nonempty
import Theorems.Thm_ThreeSum_SharedTraversalCosts_expansion_le_layer
import Theorems.Thm_ThreeSum_SharedTraversalCosts_initial_le_layer
import Theorems.Thm_ThreeSum_SharedTraversalCosts_terminal_charge_le
import Theorems.Thm_ThreeSum_SharedTraversalCosts_wanted_time_le


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
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
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
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
namespace ThreeSum.ReportingHostPrefixCatalog
end ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# Complete physical output-index decoding

The first pass writes the actual big-endian local-record digit array.
The second pass splits each digit, reads its retained layer mask, and
accumulates the occurrence-only source-bank code. Both output rows are
in forward original block order, including repeated record values.
-/

namespace ThreeSum.LightOutputDecode

open Light

set_option maxHeartbeats 2200000
set_option maxRecDepth 8000










































variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {k J T M masks dst work V U : ℕ} {f : ℕ → ℕ}




























































































































































theorem time_bound (J V : ℕ) :
    time J V ≤ 500*(J+1)*(Nat.log 2 (V+1)+2) := by
  unfold time LightOutputDecodeDigits.time LightOutputDecodeStep.time
    LightOutputDecodeDivide.budget
  nlinarith

end ThreeSum.LightOutputDecode

end

section


/-!
# Decode an actual emitted wanted-pair cell

The host loads the two physical indices, splits the left index into its
incidence position and lift, and decodes the right index into the original
occurrence and Q-mask rows. Its four-cell header retains both source labels
and the occurrence-only bank index. Division is the verified binary routine.
-/

namespace ThreeSum.LightWantedDecode

open Light GlobalEncoding OutputDecodeRecords

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000




































variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {pairs slot N h J masks dst work i j V : ℕ}



































































































































theorem time_bound (J V : ℕ) :
    time J V ≤ 800*(J+1)*(Nat.log 2 (V+1)+2) := by
  have hh := LightOutputDecode.time_bound J V
  unfold time LightOutputDecodeDivide.budget
  nlinarith

end ThreeSum.LightWantedDecode

end

section


/-!
# The executable integer cubic switch

The implementation scans integers `q ≤ r/2` and tests a cleared integer
inequality.  No real-number comparison, logarithm oracle, or unbounded
noncomputable search occurs in the definition.  For admissible depths the
candidate set is nonempty.  Minimality gives the exact `9/r` rounding error
needed by the certified box and entropy bounds.
-/

namespace ThreeSum.Switch

open Set ThreeSum.Parameters ThreeSum.Scales

set_option maxHeartbeats 0






















@[simp] theorem mem_candidates {J j r q : ℕ} :
    q ∈ candidates J j r ↔ q ≤ r / 2 ∧ accepts J j r q := by
  simp [candidates, Nat.lt_succ_iff]

theorem switchIndex_mem {J j r : ℕ} (h : (candidates J j r).Nonempty) :
    switchIndex J j r ∈ candidates J j r := by
  simp only [switchIndex, dif_pos h]
  exact Finset.min'_mem _ _







noncomputable section








































































































































theorem actual_depth_condition {n j : ℕ} (hj : j ≤ terminalDepth n) :
    20 * j ≤ 13 * blockCount (inputBits n) := by
  have hm := Nat.div_mul_le_self (13 * blockCount (inputBits n)) 20
  unfold terminalDepth at hj
  omega




























































end
end ThreeSum.Switch

end

section


/-!
# Charge the complete shared reporting catalog constructor

The actual prefix constructor enumerates the local balanced pairs even at
level zero. That additive local cost is included explicitly and bounded by
the existing local-search factor. Prefix generation, suffix tables and the
sorted physical lookup index are all charged in the complete bound below.
-/

namespace ThreeSum.SharedReportingCosts

open Scales CostLedger ReportingHostPrefixCatalog

set_option maxHeartbeats 1700000
set_option maxRecDepth 10000
























































































theorem terminal_le_blocks (n : ℕ) : Switch.terminalDepth n ≤ blocks n := by
  have hh := Switch.actual_depth_condition (n := n) (le_refl (Switch.terminalDepth n))
  change 20*Switch.terminalDepth n ≤ 13*blocks n at hh
  omega























end ThreeSum.SharedReportingCosts

end

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


































































theorem wanted_decode_log_le (n : ℕ) :
    Nat.log 2 (wantedDecodeV n+1) ≤ 8192*(inputBits n+1)+1 := by
  have hp : 1≤wantedDecodeV n := Nat.one_le_pow _ _ (by decide)
  have hb : wantedDecodeV n+1 ≤ 2^(8192*(inputBits n+1)+1) := by
    unfold wantedDecodeV at *
    rw [pow_succ]
    omega
  exact (Nat.log_mono_right (b := 2) hb).trans (by simp)


























end ThreeSum.SharedReportingBankResourceBounds

end

section


/-!
# Polynomial overhead of the actual traversal operations

All logarithmic residue costs are bounded before the binomial work terms
are charged. This prevents an endpoint magnitude from being used as a
running-time bound. The final scalar overhead is polynomial in the block
dimensions and will therefore have exponent zero at the prescribed scales.
-/

namespace ThreeSum.SharedTraversalCosts

open Finset Light LocalCoverBounds LightBlockQuery ReportingHostLevelData
open SubsetAddress
open scoped BigOperators

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000




theorem size_bounds (h J : ℕ) :
    1 ≤ size h J ∧ J+1 ≤ size h J ∧ 512*h+1 ≤ size h J ∧
      width h J+1 ≤ size h J ∧
      1026*h+4 ≤ size h J ∧
      J*(512*h)+(514*h+2)*(J+1)+2 ≤ size h J := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> simp only [size,width] <;> nlinarith






















































































































































































end ThreeSum.SharedTraversalCosts

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

theorem group_eq (n : ℕ) : groupSize (half n)=microPartitions n := by
  have hsize : 2*half n=muZero n := rfl
  have hhalf : muZero n/2=half n := by omega
  simp only [groupSize,microPartitions,hsize,hhalf]

theorem terminal_le_blocks (n : ℕ) : Switch.terminalDepth n ≤ blocks n :=
  SharedReportingCosts.terminal_le_blocks n



theorem switch_le_half {n k : ℕ} (hk : k ≤ Switch.terminalDepth n) :
    Switch.actualSwitch n k ≤ Switch.residualSize n k/2 := by
  have hn := SharedReportingBankLevels.candidates_nonempty
    (h := half n) (J := blocks n) (k := k) hk
  have hm := (Switch.mem_candidates.mp (Switch.switchIndex_mem hn)).1
  have hr : SharedReportingBankLevels.residual (half n) (blocks n) k=Switch.residualSize n k := by
    rw [← residual_eq]
    unfold SharedReportingBankLevels.residual residualSize
    ring
  rw [hr] at hm
  exact hm

















theorem initial_le_scaled {n : ℕ} (D : ℕ → Catalog) (hD : CatalogScales n D) :
    initialUnit (half n) (blocks n) D (Switch.terminalDepth n) ≤
      scaledOverhead n*queryTerms n 0 := by
  have ht : (D 0).t ≤ residualSize (half n) (blocks n) 0/2 := by
    rw [hD 0 (by omega),residual_eq]
    exact switch_le_half (by omega)
  have hh := initial_le_layer D (terminal_le_blocks n) ht
  simpa only [scaledOverhead,queryTerms,residual_eq,hD 0 (by omega)] using hh

theorem level_unit_le_scaled {n : ℕ} (D : ℕ → Catalog) (hD : CatalogScales n D) :
    levelUnit (half n) (blocks n) D (Switch.terminalDepth n) ≤
      scaledOverhead n*microPartitions n*allQueryTerms n := by
  have hterm (k : ℕ) (hk : k < Switch.terminalDepth n) :
      LightReportingPositiveExpand.time (half n) (blocks n) k (D (k+1)).t+200 ≤
        scaledOverhead n*microPartitions n*queryTerms n (k+1) := by
    have hkJ := hk.trans_le (terminal_le_blocks n)
    have hkp : k+1 ≤ Switch.terminalDepth n := hk
    have ht : (D (k+1)).t ≤ residualSize (half n) (blocks n) (k+1)/2 := by
      rw [hD (k+1) hkp,residual_eq]
      exact switch_le_half hkp
    have hh := expansion_le_layer hkJ ht
    simpa only [scaledOverhead,queryTerms,group_eq,residual_eq,hD (k+1) hkp] using hh
  have hs : (∑ k ∈ range (Switch.terminalDepth n), queryTerms n (k+1)) ≤ allQueryTerms n := by
    unfold allQueryTerms
    rw [sum_range_succ']
    omega
  calc
    _ ≤ ∑ k ∈ range (Switch.terminalDepth n),
        scaledOverhead n*microPartitions n*queryTerms n (k+1) :=
      sum_le_sum (fun k hk => hterm k (mem_range.mp hk))
    _ = scaledOverhead n*microPartitions n*
        (∑ k ∈ range (Switch.terminalDepth n), queryTerms n (k+1)) := (mul_sum _ _ _).symm
    _ ≤ _ := Nat.mul_le_mul_left _ hs

theorem terminal_charge_le_scaled (n : ℕ) :
    ReportingHostTerminalFrontier.charge (half n) (blocks n) (Switch.terminalDepth n)+240 ≤
      scaledOverhead n*terminalChoices n := by
  have hh := terminal_charge_le (half n) (blocks n) (Switch.terminalDepth n)
  have hp := (size_bounds (half n) (blocks n)).1
  have hpow := Nat.pow_le_pow_right hp (by decide : 2 ≤ 4)
  have hscalar : 31000*size (half n) (blocks n)^2 ≤ scaledOverhead n :=
    Nat.mul_le_mul (by decide) hpow
  have he : 2^((blocks n-Switch.terminalDepth n)*(2*half n))=terminalChoices n := rfl
  rw [he] at hh
  exact hh.trans (Nat.mul_le_mul_right _ hscalar)

theorem search_unit_le_scaled {n : ℕ} (D : ℕ → Catalog) (hD : CatalogScales n D) :
    searchUnit (half n) (blocks n) D (Switch.terminalDepth n) ≤
      scaledOverhead n*(microPartitions n*allQueryTerms n+terminalChoices n) := by
  have hl := level_unit_le_scaled D hD
  have ht := terminal_charge_le_scaled n
  unfold searchUnit
  nlinarith only [hl,ht]






























open Filter Real Parameters
open scoped Topology

noncomputable section












































end
end ThreeSum.SharedTraversalCosts

end

section


/-!
# Include the executed wanted decoder and scratch-pointer constructor

The actual physical indices have a size-only bound, independently of the
input integer magnitude. Their logarithmic decoder cost and the literal
layout power loop therefore contribute exponent zero. A fixed caller cost
is included explicitly for the remaining register loads and calls.
-/

namespace ThreeSum.SharedTraversalCosts

open Scales StageBounds CostLedger LightBlockQuery

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000





theorem dispatch_time_le (c n : ℕ) :
    LightReportingWantedDecodeAccess.time (blocks n)
        (SharedReportingBankResourceBounds.wantedDecodeV n)+
      LightReportingWantedLayout.time (half n) (blocks n)+c ≤ scalarOverhead c n := by
  have hd := LightWantedDecode.time_bound (blocks n)
    (SharedReportingBankResourceBounds.wantedDecodeV n)
  have hl := SharedReportingBankResourceBounds.wanted_decode_log_le n
  have hb := hd.trans (Nat.mul_le_mul_left (800*(blocks n+1))
    (show Nat.log 2 (SharedReportingBankResourceBounds.wantedDecodeV n+1)+2 ≤
      8192*(inputBits n+1)+3 by omega))
  unfold LightReportingWantedDecodeAccess.time LightReportingWantedLayout.time LightNatPower.time scalarOverhead
  omega


















































open Filter Real Parameters
open scoped Topology

noncomputable section



































end
end ThreeSum.SharedTraversalCosts

end

section


/-!
# Charge the actual fixed153 wanted scan and fixed154 header caller

The concrete dispatcher contributes4500 operations, and the ascending
recursion contributes300 per slot. The exact active-branch mass remains
inside the cumulative guard until the original reporting ledger is applied.
-/

namespace ThreeSum.SharedTraversalCosts

open Light Finset Scales BandScales GlobalEncoding RawIncidences RawReporting
open ReportingHostLevelData StageBounds CostLedger
open ReportingHostFrontierLayout Parameters

set_option maxHeartbeats 1800000
set_option maxRecDepth 14000






variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem actual_dispatch_step_le_sourceProof {n NL NR old threshold : ℕ}
    {cfg : LightReportingWantedDispatch.Config}
    (hcH : cfg.h=half n) (hcJ : cfg.J=blocks n)
    (p : ℕ) (shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ) (left right : ℕ→ℤ)
    (eL : Fin NL≃B) (eR : Fin NR≃C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i))
    (hvR : ∀ i : Fin NR, right i.val=c (eR i))
    (w : Wanted (half n) (blocks n) α) (D : ℕ→Catalog)
    (hD : CatalogScales n D)
    (hkey : w.1∈A ∧ globalModulus (half n) (blocks n)∣
      (a w.1%(p : ℤ)+lift w.2.1*(p : ℤ)+shift)-globalKey w.2.2) :
    let I := rawOn (half n) (blocks n) (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
    LightReportingWantedDispatch.time cfg (SharedReportingBankResourceBounds.wantedDecodeV n)
      (LightReportingWanted.time p shift left right NL NR old threshold I w D (Switch.terminalDepth n))+300 ≤
        scaledOverhead n*queryTerms n 0+scalarOverhead 4800 n+
          if threshold<old+rootMass I w then 0 else
            rootMass I w*(scaledOverhead n*(microPartitions n*allQueryTerms n+terminalChoices n)) := by
  dsimp only
  let I := rawOn (half n) (blocks n) (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
  have hr := wanted_time_le (old := old) (threshold := threshold) p shift A B C a b c
    left right eL eR hvL hvR w D (terminal_le_blocks n) hkey
  have hi := initial_le_scaled D hD
  have hw := Nat.mul_le_mul_left (rootMass I w) (search_unit_le_scaled D hD)
  have hd := dispatch_time_le 4800 n
  change LightReportingWanted.time p shift left right NL NR old threshold I w D (Switch.terminalDepth n) ≤
    initialUnit (half n) (blocks n) D (Switch.terminalDepth n)+
      (if threshold<old+rootMass I w then 0 else
        rootMass I w*searchUnit (half n) (blocks n) D (Switch.terminalDepth n)) at hr
  change LightReportingWantedDispatch.time cfg (SharedReportingBankResourceBounds.wantedDecodeV n)
      (LightReportingWanted.time p shift left right NL NR old threshold I w D (Switch.terminalDepth n))+300 ≤
    scaledOverhead n*queryTerms n 0+scalarOverhead 4800 n+
      if threshold<old+rootMass I w then 0 else
        rootMass I w*(scaledOverhead n*(microPartitions n*allQueryTerms n+terminalChoices n))
  unfold LightReportingWantedDispatch.time
  rw [hcH,hcJ]
  by_cases hg : threshold<old+rootMass I w
  · simp only [if_pos hg] at hr ⊢
    omega
  · simp only [if_neg hg] at hr ⊢
    omega




























noncomputable section














end
end ThreeSum.SharedTraversalCosts

end

universe u_1 u_2 u_3

theorem solution : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [Fintype.{u_1} α] [Fintype.{u_2} β] [Fintype.{u_3} γ]
  [inst : DecidableEq.{u_1 + 1} α] [DecidableEq.{u_2 + 1} β] [DecidableEq.{u_3 + 1} γ] {n NL NR old threshold : Nat}
  {cfg : ThreeSum.LightReportingWantedDispatch.Config},
  @Eq.{1} Nat cfg.h (ThreeSum.SharedTraversalCosts.half n) →
    @Eq.{1} Nat cfg.J (ThreeSum.SharedTraversalCosts.blocks n) →
      ∀ (p : Nat) (shift : Int) (A : Finset.{u_1} α) (B : Finset.{u_2} β) (C : Finset.{u_3} γ) (a : α → Int)
        (b : β → Int) (c : γ → Int) (left right : Nat → Int) (eL : Equiv.{1, u_2 + 1} (Fin NL) ↥B)
        (eR : Equiv.{1, u_3 + 1} (Fin NR) ↥C),
        (∀ (i : Fin NL),
            @Eq.{1} Int (left (@Fin.val NL i))
              (b
                (@Subtype.val.{u_2 + 1} β
                  (fun (x : β) =>
                    @Membership.mem.{u_2, u_2} β (Finset.{u_2} β)
                      (@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} β) β (@Finset.instSetLike.{u_2} β)) B x)
                  (@DFunLike.coe.{u_2 + 1, 1, u_2 + 1} (Equiv.{1, u_2 + 1} (Fin NL) ↥B) (Fin NL)
                    (fun (x : Fin NL) => ↥B)
                    (@EquivLike.toFunLike.{u_2 + 1, 1, u_2 + 1} (Equiv.{1, u_2 + 1} (Fin NL) ↥B) (Fin NL) (↥B)
                      (@Equiv.instEquivLike.{1, u_2 + 1} (Fin NL) ↥B))
                    eL i)))) →
          (∀ (i : Fin NR),
              @Eq.{1} Int (right (@Fin.val NR i))
                (c
                  (@Subtype.val.{u_3 + 1} γ
                    (fun (x : γ) =>
                      @Membership.mem.{u_3, u_3} γ (Finset.{u_3} γ)
                        (@SetLike.instMembership.{u_3, u_3} (Finset.{u_3} γ) γ (@Finset.instSetLike.{u_3} γ)) C x)
                    (@DFunLike.coe.{u_3 + 1, 1, u_3 + 1} (Equiv.{1, u_3 + 1} (Fin NR) ↥C) (Fin NR)
                      (fun (x : Fin NR) => ↥C)
                      (@EquivLike.toFunLike.{u_3 + 1, 1, u_3 + 1} (Equiv.{1, u_3 + 1} (Fin NR) ↥C) (Fin NR) (↥C)
                        (@Equiv.instEquivLike.{1, u_3 + 1} (Fin NR) ↥C))
                      eR i)))) →
            ∀
              (w :
                ThreeSum.RawReporting.Wanted.{u_1} (ThreeSum.SharedTraversalCosts.half n)
                  (ThreeSum.SharedTraversalCosts.blocks n) α)
              (D : Nat → ThreeSum.ReportingHostLevelData.Catalog),
              ThreeSum.SharedTraversalCosts.CatalogScales n D →
                And
                    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
                      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) A
                      (@Prod.fst.{u_1, 0} α
                        (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedTraversalCosts.half n)
                            (ThreeSum.SharedTraversalCosts.blocks n)))
                        w))
                    (@Dvd.dvd.{0} Int Int.instDvd
                      (ThreeSum.GlobalEncoding.globalModulus (ThreeSum.SharedTraversalCosts.half n)
                        (ThreeSum.SharedTraversalCosts.blocks n))
                      (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
                        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                            (@HMod.hMod.{0, 0, 0} Int Int Int (@instHMod.{0} Int Int.instMod)
                              (a
                                (@Prod.fst.{u_1, 0} α
                                  (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                    (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedTraversalCosts.half n)
                                      (ThreeSum.SharedTraversalCosts.blocks n)))
                                  w))
                              (@Nat.cast.{0} Int instNatCastInt p))
                            (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                              (ThreeSum.RawIncidences.lift
                                (@Prod.fst.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                  (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedTraversalCosts.half n)
                                    (ThreeSum.SharedTraversalCosts.blocks n))
                                  (@Prod.snd.{u_1, 0} α
                                    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                      (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedTraversalCosts.half n)
                                        (ThreeSum.SharedTraversalCosts.blocks n)))
                                    w)))
                              (@Nat.cast.{0} Int instNatCastInt p)))
                          shift)
                        (@ThreeSum.GlobalEncoding.globalKey (ThreeSum.SharedTraversalCosts.half n)
                          (ThreeSum.SharedTraversalCosts.blocks n)
                          (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedTraversalCosts.half n)
                              (ThreeSum.SharedTraversalCosts.blocks n))
                            (@Prod.snd.{u_1, 0} α
                              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedTraversalCosts.half n)
                                  (ThreeSum.SharedTraversalCosts.blocks n)))
                              w))))) →
                  have I :=
                    @ThreeSum.RawIncidences.rawOn.{u_1, u_2, u_3} α β γ (ThreeSum.SharedTraversalCosts.half n)
                      (ThreeSum.SharedTraversalCosts.blocks n) (@Nat.cast.{0} Int instNatCastInt p) shift
                      (@SProd.sprod.{u_1, max u_2 u_3, max (max u_1 u_2) u_3} (Finset.{u_1} α)
                        (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ))
                        (Finset.{max (max u_2 u_3) u_1} (Prod.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)))
                        (@Finset.instSProd.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)) A
                        (@SProd.sprod.{u_2, u_3, max u_2 u_3} (Finset.{u_2} β) (Finset.{u_3} γ)
                          (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ)) (@Finset.instSProd.{u_2, u_3} β γ) B C))
                      a b c;
                  @LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (ThreeSum.LightReportingWantedDispatch.time cfg
                        (ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n)
                        (@ThreeSum.LightReportingWanted.time.{u_1, u_2, u_3} α β γ inst
                          (ThreeSum.SharedTraversalCosts.half n) (ThreeSum.SharedTraversalCosts.blocks n) p shift left
                          right NL NR old threshold I w D (ThreeSum.Switch.terminalDepth n)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 300) (instOfNatNat (nat_lit 300))))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (ThreeSum.SharedTraversalCosts.scaledOverhead n)
                          (ThreeSum.CostLedger.queryTerms n
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                        (ThreeSum.SharedTraversalCosts.scalarOverhead
                          (@OfNat.ofNat.{0} Nat (nat_lit 4800) (instOfNatNat (nat_lit 4800))) n))
                      (@ite.{1} Nat
                        (@LT.lt.{0} Nat instLTNat threshold
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
                            (@ThreeSum.ReportingHostFrontierLayout.rootMass.{u_1, u_2, u_3} α β γ inst
                              (ThreeSum.SharedTraversalCosts.half n) (ThreeSum.SharedTraversalCosts.blocks n) I w)))
                        (threshold.decLt
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
                            (@ThreeSum.ReportingHostFrontierLayout.rootMass.{u_1, u_2, u_3} α β γ inst
                              (ThreeSum.SharedTraversalCosts.half n) (ThreeSum.SharedTraversalCosts.blocks n) I w)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@ThreeSum.ReportingHostFrontierLayout.rootMass.{u_1, u_2, u_3} α β γ inst
                            (ThreeSum.SharedTraversalCosts.half n) (ThreeSum.SharedTraversalCosts.blocks n) I w)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (ThreeSum.SharedTraversalCosts.scaledOverhead n)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (ThreeSum.CostLedger.microPartitions n) (ThreeSum.CostLedger.allQueryTerms n))
                              (ThreeSum.StageBounds.terminalChoices n)))))) := by
  exact @ThreeSum.SharedTraversalCosts.actual_dispatch_step_le_sourceProof

#print axioms solution

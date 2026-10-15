-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.candidates_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:10:10.542115+00:00
-- url     : https://prove2.me/submissions/f710fa16-f909-4908-b94d-6f464458d25b

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
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
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
import Definitions.Def_ThreeSum1960614_Machine_Bundle025
import Definitions.Def_ThreeSum1960614_Machine_Bundle026
import Definitions.Def_ThreeSum1960614_Machine_Bundle027
import Definitions.Def_ThreeSum1960614_Machine_Bundle028
import Definitions.Def_ThreeSum1960614_Machine_Bundle029
import Definitions.Def_ThreeSum1960614_Machine_Bundle030
import Definitions.Def_ThreeSum1960614_Machine_Bundle031
import Definitions.Def_ThreeSum1960614_Machine_Bundle032
import Definitions.Def_ThreeSum1960614_Machine_Bundle033
import Definitions.Def_ThreeSum1960614_Machine_Bundle034
import Definitions.Def_ThreeSum1960614_Machine_Bundle035
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
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
import Lean
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
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
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

namespace Light
end Light
namespace Set
end Set
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.Switch
end ThreeSum.Switch
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.Switch
end ThreeSum1960614.Machine.ThreeSum.Switch

namespace ThreeSum1960614.Machine

/-!
Expansion-232 analytic interface for the actual machine-source modules.
The definition bodies use the audited rational quartic parameter choice.
Closed analytic proofs supply the bounds; no program correctness contract
is assumed by this interface. Additional operational exponents must remain
the individual raw ledger costs for the universal rational-r bridge.
-/

noncomputable section
namespace ThreeSum.Parameters
open _root_.ThreeSum.Parameters

open _root_.Set











































theorem phi_half : _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi (1/2)=(6631298715/1600000000 : ℝ) := by norm_num [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi]
















theorem switchThreshold_upper {a : ℝ} (ha : a ∈ Icc (0 : ℝ) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.switchThreshold a ≤ 3 := by
  have hden : 0 < 1-a := by dsimp [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction] at ha; linarith [ha.2]
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.switchThreshold,div_le_iff₀ hden]
  dsimp [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction] at *
  linarith [ha.2]





end ThreeSum.Parameters

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The executable integer quartic switch

The implementation scans integers `q ≤ r/2` and tests a cleared integer
inequality.  No real-number comparison, logarithm oracle, or unbounded
noncomputable search occurs in the definition.  For admissible depths the
candidate set is nonempty.  Minimality gives the exact `9/r` rounding error
needed by the certified box and entropy bounds.
-/

namespace ThreeSum.Switch
open _root_.ThreeSum.Switch


open _root_.Set
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales

set_option maxHeartbeats 0





theorem accepts_expanded (J j r q : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts J j r q ↔
      100000000*(159243801*J+500000000*j)*r^4 ≤ 500000000*(J-j)*_root_.ThreeSum1960614.Machine.ThreeSum.Switch.quarticNumerator r q := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.accepts
    _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.left _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.factor
    _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.polynomial _root_.ThreeSum1960614.Machine.ThreeSum.Switch.quarticNumerator
  ring_nf













@[simp] theorem mem_candidates {J j r q : ℕ} :
    q ∈ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates J j r ↔ q ≤ r / 2 ∧ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts J j r q := by
  simp [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates, Nat.lt_succ_iff]





noncomputable section

theorem depth_fraction {J j : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J) :
    (j : ℝ) / J ∈ Icc (0 : ℝ) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  constructor
  · positivity
  · rw [div_le_iff₀ hJR]
    have ht : (20 : ℝ) * j ≤ 13 * J := by exact_mod_cast hj
    dsimp [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction]
    linarith

theorem depth_lt {J j : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J) : j < J := by
  omega

theorem threshold_fraction {J j : ℕ} (hJ : 0 < J) (hj : j < J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.switchThreshold ((j : ℝ) / J) =
      (159243801*(J : ℝ)+500000000*j)/(500000000*((J-j : ℕ) : ℝ)) := by
  have hJR : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  have hd : ((J - j : ℕ) : ℝ) = (J : ℝ) - j := by
    exact Nat.cast_sub hj.le
  have hden : (J : ℝ) - j ≠ 0 := by
    have hlt : (j : ℝ) < J := by exact_mod_cast hj
    linarith
  rw [hd]
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.switchThreshold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift
  field_simp
  <;> ring

theorem phi_fraction {r q : ℕ} (hr : 0 < r) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi ((q : ℝ) / r) = (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.quarticNumerator r q : ℝ)/(100000000*(r : ℝ)^4) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi,_root_.ThreeSum1960614.Machine.ThreeSum.Switch.quarticNumerator,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  field_simp
  <;> ring

theorem accepts_iff {J j r q : ℕ} (hJ : 0 < J) (hj : j < J) (hr : 0 < r) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts J j r q ↔ _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.switchThreshold ((j : ℝ) / J) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi ((q : ℝ) / r) := by
  have hd : (0 : ℝ) < ((J - j : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hj
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.threshold_fraction hJ hj, _root_.ThreeSum1960614.Machine.ThreeSum.Switch.phi_fraction hr, div_le_div_iff₀ (by positivity) (by positivity)]
  have hc : _root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts J j r q ↔
      100000000*(159243801*(J : ℝ)+500000000*j)*(r : ℝ)^4 ≤
        500000000*((J-j : ℕ) : ℝ)*(_root_.ThreeSum1960614.Machine.ThreeSum.Switch.quarticNumerator r q : ℝ) := by
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts_expanded]
    exact_mod_cast Iff.rfl
  rw [hc]
  constructor <;> intro h <;> nlinarith

theorem half_fraction {r : ℕ} (hr : 0 < r) (heven : 2 ∣ r) :
    ((r / 2 : ℕ) : ℝ) / r = (1 / 2 : ℝ) := by
  have hm := Nat.div_mul_cancel heven
  have hmR : ((r / 2 : ℕ) : ℝ) * 2 = r := by exact_mod_cast hm
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp
  linarith

theorem candidates_nonempty {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) : (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates J j r).Nonempty := by
  refine ⟨r / 2, _root_.ThreeSum1960614.Machine.ThreeSum.Switch.mem_candidates.mpr ⟨le_rfl, ?_⟩⟩
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts_iff hJ (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.depth_lt hJ hj) hr, _root_.ThreeSum1960614.Machine.ThreeSum.Switch.half_fraction hr heven, _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi_half]
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.switchThreshold_upper (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.depth_fraction hJ hj)
  linarith



























end
end ThreeSum.Switch

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
set_option maxHeartbeats 1400000
section

theorem ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.candidates_nonempty__implementation_55971d99dd {h J k : ℕ} (hk : k ≤ _root_.ThreeSum.LightSwitchDepth.depth J) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates J k (_root_.ThreeSum.SharedReportingBankLevels.residual h J k)).Nonempty := by
  by_cases hz : _root_.ThreeSum.SharedReportingBankLevels.residual h J k=0
  · refine ⟨0,_root_.ThreeSum1960614.Machine.ThreeSum.Switch.mem_candidates.mpr ⟨by omega,?_⟩⟩
    simp [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts,_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.accepts,
      _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.left,_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.polynomial,hz]
  · have hJ : 0 < J := by
      by_contra h
      have he : J=0 := by omega
      simp [_root_.ThreeSum.SharedReportingBankLevels.residual,he] at hz
    have hdepth : 20*k ≤ 13*J := by
      have hd := Nat.div_mul_le_self (13*J) 20
      unfold _root_.ThreeSum.LightSwitchDepth.depth at hk
      omega
    exact _root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates_nonempty hJ hdepth (by omega)
      ⟨h*(J-k),by unfold _root_.ThreeSum.SharedReportingBankLevels.residual; ring⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.candidates_nonempty__implementation_55971d99dd) := (@ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.candidates_nonempty__implementation_55971d99dd)

#print axioms solution

-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.Switch.actual_switch_certified
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:09:11.083033+00:00
-- url     : https://prove2.me/submissions/d2346cd1-782c-476c-b0fa-3f0570de41ec

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
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
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Pow
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
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_Parameters_switch_entropy_bound
import Theorems.Thm_ThreeSum1960614_quartic_switch_bounds

local instance platformRadixNonzero_edbcff13ae (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Filter
end Filter
namespace Real
end Real
namespace Set
end Set
namespace ThreeSum
end ThreeSum
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.Switch
end ThreeSum.Switch
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
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


theorem phi_derivative_lt_nine {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1/2)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phiDeriv t < 9 := by
  have h := (_root_.ThreeSum1960614.quartic_switch_bounds t ht).2.2.1
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phiDeriv,_root_.ThreeSum1960614.phiDeriv] using h

theorem phi_le_gamma {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1/2)) : _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi t ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.gamma t := by
  have h := (_root_.ThreeSum1960614.quartic_switch_bounds t ht).1
  norm_num [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.gamma,_root_.ThreeSum.Parameters.entropy,_root_.ThreeSum1960614.phi,_root_.ThreeSum1960614.gamma,
    _root_.ThreeSum1960614.entropy] at h ⊢
  exact h



theorem hasDerivAt_phi (t : ℝ) : HasDerivAt _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phiDeriv t) t := by
  have hd := (((((hasDerivAt_id t).const_mul 785174904).add
    (((hasDerivAt_id t).pow 2).const_mul 72447023)).add
      (((hasDerivAt_id t).pow 3).const_mul 24044466)).add
        (((hasDerivAt_id t).pow 4).const_mul 12022459)).div_const 100000000
  change HasDerivAt _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi _ t at hd
  apply hd.congr_deriv
  dsimp [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phiDeriv]
  ring

theorem phi_increment_bound {u v : ℝ}
    (hu : u ∈ Icc (0 : ℝ) (1/2)) (hv : v ∈ Icc (0 : ℝ) (1/2)) (huv : u < v) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi v-_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi u < 9*(v-u) := by
  apply (convex_Icc (0 : ℝ) (1/2)).image_sub_lt_mul_sub_of_deriv_lt
    (fun y _ => (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.hasDerivAt_phi y).continuousAt.continuousWithinAt)
    (fun y _ => (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.hasDerivAt_phi y).differentiableAt.differentiableWithinAt)
    (fun y hy => ?_) u hu v hv huv
  rw [(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.hasDerivAt_phi y).deriv]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi_derivative_lt_nine (interior_subset hy)

theorem phi_step_rounding {u v m K : ℝ}
    (hu : u ∈ Icc (0 : ℝ) (1/2)) (hv : v ∈ Icc (0 : ℝ) (1/2))
    (hm : 0 < m) (hstep : v-u=1/m) (hprev : _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi u < K) : _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi v < K+9/m := by
  have huv : u < v := by
    have hpositive : 0 < 1/m := by positivity
    linarith
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi_increment_bound hu hv huv
  rw [hstep] at h
  rw [show 9/m=9*(1/m) by ring]
  linarith



theorem switchThreshold_upper {a : ℝ} (ha : a ∈ Icc (0 : ℝ) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.switchThreshold a ≤ 3 := by
  have hden : 0 < 1-a := by dsimp [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction] at ha; linarith [ha.2]
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.switchThreshold,div_le_iff₀ hden]
  dsimp [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction] at *
  linarith [ha.2]

theorem switch_box_bound {a t : ℝ} (ha : a ∈ Icc (0 : ℝ) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction)
    (ht : t ∈ Icc (0 : ℝ) (1/2)) (hswitch : _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.switchThreshold a ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi t) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving ≤ 2*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift-a+(1-a)*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.gamma t := by
  have hden : 0 < 1-a := by dsimp [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction] at ha; linarith [ha.2]
  have hs := (div_le_iff₀ hden).mp hswitch
  have hg := mul_le_mul_of_nonneg_left (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi_le_gamma ht) hden.le
  linarith



end ThreeSum.Parameters

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The actual integer block schedule

All four size parameters below are executable natural-number functions.
The finite bounds and limits concern these functions, including the even
rounding of the cube root and the divisibility constraints on the number
of blocks.  No asymptotic size premise is imposed on the schedule.
-/

namespace ThreeSum.Scales
open _root_.ThreeSum.Scales


open _root_.Filter
open _root_.Real
open scoped _root_.Topology







































theorem microSize_even (m : ℕ) : 2 ∣ _root_.ThreeSum.Scales.microSize m := by
  exact ⟨Nat.nthRoot 3 m / 2, rfl⟩













noncomputable section







































































































































end

end ThreeSum.Scales

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

theorem switchIndex_mem {J j r : ℕ} (h : (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates J j r).Nonempty) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J j r ∈ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates J j r := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex, dif_pos h]
  exact Finset.min'_mem _ _

theorem switchIndex_le {J j r q : ℕ} (hq : q ∈ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates J j r) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J j r ≤ q := by
  have h : (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates J j r).Nonempty := ⟨q, hq⟩
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex, dif_pos h]
  exact Finset.min'_le _ _ hq

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

theorem switchIndex_spec {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J j r ≤ r / 2 ∧ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts J j r (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J j r) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.Switch.mem_candidates.mp (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex_mem (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates_nonempty hJ hj hr heven))

theorem switchIndex_pos {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J j r := by
  have hs := (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex_spec hJ hj hr heven).2
  by_contra hn
  have hz : _root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J j r = 0 := by omega
  rw [hz] at hs
  have hp : 0 < _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.left J j r := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.left
    positivity
  simp [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts,_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.accepts,
    _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.polynomial] at hs
  omega

theorem predecessor_rejected {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) :
    ¬ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts J j r (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J j r - 1) := by
  have hpos := _root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex_pos hJ hj hr heven
  have hle := (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex_spec hJ hj hr heven).1
  intro ha
  have hm : _root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J j r - 1 ∈ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates J j r :=
    _root_.ThreeSum1960614.Machine.ThreeSum.Switch.mem_candidates.mpr ⟨by omega, ha⟩
  have hbad := _root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex_le hm
  omega

theorem ratio_mem_half {r q : ℕ} (hr : 0 < r) (hq : q ≤ r / 2) :
    (q : ℝ) / r ∈ Icc (0 : ℝ) (1 / 2) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have htwo : 2 * q ≤ r := by
    have hm := Nat.div_mul_le_self r 2
    omega
  have htwoR : (2 : ℝ) * q ≤ r := by exact_mod_cast htwo
  constructor
  · positivity
  · rw [div_le_iff₀ hrR]
    linarith

theorem switch_ratio_mem {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J j r : ℝ) / r ∈ Icc (0 : ℝ) (1 / 2) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.Switch.ratio_mem_half hr (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex_spec hJ hj hr heven).1

theorem phi_enclosure {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.switchThreshold ((j : ℝ) / J) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi ((_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J j r : ℝ) / r) ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi ((_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J j r : ℝ) / r) <
        _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.switchThreshold ((j : ℝ) / J) + 9 / r := by
  have hlt := _root_.ThreeSum1960614.Machine.ThreeSum.Switch.depth_lt hJ hj
  have hspec := _root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex_spec hJ hj hr heven
  constructor
  · exact (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts_iff hJ hlt hr).mp hspec.2
  · have hpos := _root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex_pos hJ hj hr heven
    have hpre : _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi (((_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J j r - 1 : ℕ) : ℝ) / r) <
        _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.switchThreshold ((j : ℝ) / J) := by
      apply lt_of_not_ge
      intro ha
      exact _root_.ThreeSum1960614.Machine.ThreeSum.Switch.predecessor_rejected hJ hj hr heven ((_root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts_iff hJ hlt hr).mpr ha)
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    have hpR : ((_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J j r - 1 : ℕ) : ℝ) = (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J j r : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    apply _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi_step_rounding
      (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.ratio_mem_half hr (show _root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J j r - 1 ≤ r / 2 by omega))
      (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switch_ratio_mem hJ hj hr heven) hrR ?_ hpre
    rw [hpR]
    field_simp
    <;> ring

theorem actual_totalSize (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n = _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) * _root_.ThreeSum.Scales.muZero n := rfl

theorem actual_residual_even (n j : ℕ) : 2 ∣ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n j := by
  exact dvd_mul_of_dvd_right (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.microSize_even (_root_.ThreeSum.Scales.inputBits n)) _

theorem actual_depth_condition {n j : ℕ} (hj : j ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n) :
    20 * j ≤ 13 * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) := by
  have hm := Nat.div_mul_le_self (13 * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) 20
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth at hj
  omega

theorem actual_residual_pos {n j : ℕ} (hmu : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) (hj : j ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n) :
    0 < _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n j := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_totalSize] at hmu
  have hp := And.intro (Nat.pos_of_mul_pos_right hmu) (Nat.pos_of_mul_pos_left hmu)
  have hd := _root_.ThreeSum1960614.Machine.ThreeSum.Switch.depth_lt hp.1 (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_depth_condition hj)
  exact Nat.mul_pos (Nat.sub_pos_of_lt hd) hp.2

theorem residual_real_identity {n j : ℕ} (hmu : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)
    (hj : j ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n j : ℝ) =
      (1 - (j : ℝ) / _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by
  have hm := hmu
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_totalSize] at hm
  have hp := And.intro (Nat.pos_of_mul_pos_right hm) (Nat.pos_of_mul_pos_left hm)
  have hlt := _root_.ThreeSum1960614.Machine.ThreeSum.Switch.depth_lt hp.1 (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_depth_condition hj)
  have hJ : (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) : ℝ) ≠ 0 := by exact_mod_cast hp.1.ne'
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize, _root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_totalSize, Nat.cast_mul, Nat.cast_sub hlt.le]
  field_simp
  <;> ring





end
end ThreeSum.Switch

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.Switch

open _root_.Set
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
set_option maxHeartbeats 0
open _root_.ThreeSum1960614.Machine.ThreeSum.Switch

section

theorem ThreeSum1960614.Machine.ThreeSum.Switch.actual_switch_certified__implementation_1c8f7d98d6 {n j : ℕ} (hmu : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)
    (hj : j ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n) :
    let a : ℝ := (j : ℝ) / _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)
    let t : ℝ := (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch n j : ℝ) / _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n j
    t ∈ Icc (0 : ℝ) (1 / 2) ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving ≤ 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift - a + (1 - a) * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.gamma t ∧
      (1 - a) * _root_.ThreeSum.Parameters.entropy t <
        _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio * (1 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving - 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift) + 9 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio / _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by
  dsimp only
  have hm := hmu
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_totalSize] at hm
  have hp := And.intro (Nat.pos_of_mul_pos_right hm) (Nat.pos_of_mul_pos_left hm)
  have hdepth := _root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_depth_condition hj
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_residual_pos hmu hj
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_residual_even n j
  have ha := _root_.ThreeSum1960614.Machine.ThreeSum.Switch.depth_fraction hp.1 hdepth
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.Switch.switch_ratio_mem hp.1 hdepth hr he
  have hf := _root_.ThreeSum1960614.Machine.ThreeSum.Switch.phi_enclosure hp.1 hdepth hr he
  change ((_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex _ _ _ : ℝ) / _) ∈ _ ∧ _
  refine ⟨ht, _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.switch_box_bound ha ht hf.1, ?_⟩
  apply _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.switch_entropy_bound ha ht (by exact_mod_cast hmu)
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residual_real_identity hmu hj]
  exact hf.2
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.Switch.actual_switch_certified__implementation_1c8f7d98d6) := (@ThreeSum1960614.Machine.ThreeSum.Switch.actual_switch_certified__implementation_1c8f7d98d6)

#print axioms solution

-- Prove2me | solution 1 for ThreeSum.HierarchyScales.initial_query_eventually_le
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:09:46.111423+00:00
-- url     : https://prove2.me/submissions/5a147e2d-0dac-44b1-b73e-2b133889f3ab

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
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
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_Switch_actual_switch_certified


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.Switch
end ThreeSum.Switch

section


/-!
# Analytic and rational parameter certificate for the proposed 3SUM algorithm

This module certifies the real-variable inequalities and the resulting exponent ledger.
It does not by itself prove that an implementation has those costs: the reduction,
cover, encoding, reporting, arithmetic and machine-model lemmas are separate obligations.

All decimal-looking constants below are exact rational numbers. There are no numerical
oracles, admitted declarations, or native-code decision procedures in this certificate.
-/

noncomputable section

namespace ThreeSum.Parameters

open Set Real

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048







































/-! ## Exact integer witnesses for the logarithmic comparisons -/































































































































































/-! ## Exact rational inequalities for the schedule -/



theorem phi_half : phi (1 / 2) = (841 / 200 : ℝ) := by norm_num [phi]

























































































































































































































theorem switchThreshold_upper {a : ℝ} (ha : a ∈ Icc (0 : ℝ) terminalFraction) :
    switchThreshold a ≤ 941 / 350 := by
  have hden : 0 < 1 - a := by dsimp [terminalFraction] at ha; linarith [ha.2]
  rw [switchThreshold, div_le_iff₀ hden]
  dsimp [boxSaving, bandShift, terminalFraction] at *
  linarith [ha.2]














































/-! ## The real-valued ledger, before the algorithmic cost lemmas are applied -/





























































end ThreeSum.Parameters

end
end

section


/-!
# The actual integer block schedule

All four size parameters below are executable natural-number functions.
The finite bounds and limits concern these functions, including the even
rounding of the cube root and the divisibility constraints on the number
of blocks.  No asymptotic size premise is imposed on the schedule.
-/

namespace ThreeSum.Scales

open Filter Real
open scoped Topology













































theorem microSize_even (m : ℕ) : 2 ∣ microSize m := by
  exact ⟨Nat.nthRoot 3 m / 2, rfl⟩


































noncomputable section



























































































































































































































































































































































































































































































































































































































































































































































































































































end

end ThreeSum.Scales

end

section


/-!
# Actual vertex and trimmed-bucket scales

The local prime and bucket cap are the computable finite selections from
`LocalCoverBounds`.  Their logarithmic rates are derived from those exact
definitions and the exact integer schedule in `Scales`.
-/

namespace ThreeSum.TrimScales

open Filter Real ThreeSum.Scales
open scoped Topology






















noncomputable section





















































































































































































































theorem mu_cast_tendsto_atTop : Tendsto (fun n : ℕ => (mu n : ℝ)) atTop atTop := by
  have hpos : (0 : ℝ) < 1 / (5 * Real.log 2) := by positivity
  have h := mu_log_ratio_tendsto.pos_mul_atTop hpos Asymptotics.log_nat_tendsto_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hlog : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
  exact div_mul_cancel₀ _ hlog

theorem mu_tendsto_atTop : Tendsto mu atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [mu_cast_tendsto_atTop.eventually (eventually_ge_atTop (b : ℝ))] with n hn
  exact_mod_cast hn
































































end

end ThreeSum.TrimScales

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

theorem switchIndex_le {J j r q : ℕ} (hq : q ∈ candidates J j r) :
    switchIndex J j r ≤ q := by
  have h : (candidates J j r).Nonempty := ⟨q, hq⟩
  simp only [switchIndex, dif_pos h]
  exact Finset.min'_le _ _ hq

noncomputable section

theorem depth_fraction {J j : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J) :
    (j : ℝ) / J ∈ Icc (0 : ℝ) terminalFraction := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  constructor
  · positivity
  · rw [div_le_iff₀ hJR]
    have ht : (20 : ℝ) * j ≤ 13 * J := by exact_mod_cast hj
    dsimp [terminalFraction]
    linarith

theorem depth_lt {J j : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J) : j < J := by
  omega

theorem threshold_fraction {J j : ℕ} (hJ : 0 < J) (hj : j < J) :
    switchThreshold ((j : ℝ) / J) =
      (291 * (J : ℝ) + 1000 * j) / (1000 * ((J - j : ℕ) : ℝ)) := by
  have hJR : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  have hd : ((J - j : ℕ) : ℝ) = (J : ℝ) - j := by
    exact Nat.cast_sub hj.le
  have hden : (J : ℝ) - j ≠ 0 := by
    have hlt : (j : ℝ) < J := by exact_mod_cast hj
    linarith
  rw [hd]
  unfold switchThreshold boxSaving bandShift
  field_simp
  <;> ring

theorem phi_fraction {r q : ℕ} (hr : 0 < r) :
    phi ((q : ℝ) / r) = (cubicNumerator r q : ℝ) / (100 * (r : ℝ) ^ 3) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [phi, cubicNumerator, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  <;> ring

theorem accepts_iff {J j r q : ℕ} (hJ : 0 < J) (hj : j < J) (hr : 0 < r) :
    accepts J j r q ↔ switchThreshold ((j : ℝ) / J) ≤ phi ((q : ℝ) / r) := by
  have hd : (0 : ℝ) < ((J - j : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hj
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  rw [threshold_fraction hJ hj, phi_fraction hr, div_le_div_iff₀ (by positivity) (by positivity)]
  have hc : accepts J j r q ↔
      (291 * (J : ℝ) + 1000 * j) * (r : ℝ) ^ 3 ≤
        10 * ((J - j : ℕ) : ℝ) * (cubicNumerator r q : ℝ) := by
    unfold accepts
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
    (hr : 0 < r) (heven : 2 ∣ r) : (candidates J j r).Nonempty := by
  refine ⟨r / 2, mem_candidates.mpr ⟨le_rfl, ?_⟩⟩
  rw [accepts_iff hJ (depth_lt hJ hj) hr, half_fraction hr heven, phi_half]
  have h := switchThreshold_upper (depth_fraction hJ hj)
  linarith

theorem switchIndex_spec {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) :
    switchIndex J j r ≤ r / 2 ∧ accepts J j r (switchIndex J j r) :=
  mem_candidates.mp (switchIndex_mem (candidates_nonempty hJ hj hr heven))
































































theorem actual_totalSize (n : ℕ) : mu n = blockCount (inputBits n) * muZero n := rfl

theorem actual_residual_even (n j : ℕ) : 2 ∣ residualSize n j := by
  exact dvd_mul_of_dvd_right (microSize_even (inputBits n)) _

theorem actual_depth_condition {n j : ℕ} (hj : j ≤ terminalDepth n) :
    20 * j ≤ 13 * blockCount (inputBits n) := by
  have hm := Nat.div_mul_le_self (13 * blockCount (inputBits n)) 20
  unfold terminalDepth at hj
  omega

theorem actual_residual_pos {n j : ℕ} (hmu : 0 < mu n) (hj : j ≤ terminalDepth n) :
    0 < residualSize n j := by
  rw [actual_totalSize] at hmu
  have hp := And.intro (Nat.pos_of_mul_pos_right hmu) (Nat.pos_of_mul_pos_left hmu)
  have hd := depth_lt hp.1 (actual_depth_condition hj)
  exact Nat.mul_pos (Nat.sub_pos_of_lt hd) hp.2





















































end
end ThreeSum.Switch

end

section


/-!
# Finite sums and asymptotic bounds for the actual hierarchy

The finite box and query counts are summed over the executable depth range.
The only envelopes introduced here are explicit elementary functions of the
already constructed integer `mu`; all growth rates are proved from Scales.
-/

namespace ThreeSum.HierarchyScales

open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000





theorem initialCap_bounds (r : ℕ) : r ≤ 25 * initialCap r ∧ 25 * initialCap r < r + 25 := by
  constructor
  · exact (ceilDiv_le_iff_le_mul (a := 25) (b := r)
      (c := initialCap r) (by norm_num)).mp le_rfl
  · have h := Nat.div_mul_le_self (r + 25 - 1) 25
    simp only [initialCap, Nat.ceilDiv_eq_add_pred_div]
    omega

theorem initialCap_accepted (J r : ℕ) : accepts J 0 r (initialCap r) := by
  have hh := Nat.mul_le_mul_right (r ^ 2) (initialCap_bounds r).1
  have hm := Nat.mul_le_mul_left (291 * J) hh
  unfold accepts cubicNumerator
  simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero]
  ring_nf at hm ⊢
  omega

theorem initialIndex_le_cap (J : ℕ) {r : ℕ} (hr : 50 ≤ r) :
    switchIndex J 0 r ≤ initialCap r := by
  apply switchIndex_le
  apply mem_candidates.mpr
  refine ⟨?_, initialCap_accepted J r⟩
  have h := (initialCap_bounds r).2
  omega

theorem residual_zero (n : ℕ) : residualSize n 0 = mu n := by
  simp only [residualSize, Nat.sub_zero, actual_totalSize]










noncomputable section



















































































































theorem initial_ratio_le {n : ℕ} (hmu : 50 ≤ mu n) :
    (actualSwitch n 0 : ℝ) / mu n ≤ initialTheta + 1 / mu n := by
  have hq := initialIndex_le_cap (blockCount (inputBits n)) hmu
  have hc := (initialCap_bounds (mu n)).2
  have hq' : actualSwitch n 0 ≤ initialCap (mu n) := by
    simpa only [actualSwitch, residual_zero] using hq
  have hbound : (25 : ℝ) * actualSwitch n 0 < (mu n : ℝ) + 25 := by exact_mod_cast lt_of_le_of_lt (Nat.mul_le_mul_left 25 hq') hc
  have hmuR : (0 : ℝ) < mu n := by exact_mod_cast (by omega : 0 < mu n)
  rw [div_le_iff₀ hmuR]
  have hid : (initialTheta + 1 / (mu n : ℝ)) * mu n = (mu n : ℝ) / 25 + 1 := by
    unfold initialTheta
    field_simp
  rw [hid]
  linarith

theorem initial_upper_mem {n : ℕ} (hmu : 50 ≤ mu n) :
    initialTheta + 1 / (mu n : ℝ) ∈ Icc (0 : ℝ) (1 / 2) := by
  have hm : (50 : ℝ) ≤ mu n := by exact_mod_cast hmu
  have hp : (0 : ℝ) < mu n := by linarith
  have hu : 1 / (mu n : ℝ) ≤ 1 / 50 := one_div_le_one_div_of_le (by norm_num) hm
  constructor
  · unfold initialTheta; positivity
  · unfold initialTheta; linarith

theorem initial_query_log_bound {n : ℕ} (hmu : 50 ≤ mu n) :
    Real.log (queryTerms n 0 : ℝ) ≤
      (mu n : ℝ) * Real.log 2 * entropy (initialTheta + 1 / (mu n : ℝ)) := by
  have hm : 0 < mu n := by omega
  have ht := (actual_switch_certified (j := 0) hm (by omega)).1
  rw [residual_zero] at ht
  have hupper := initial_upper_mem hmu
  have hmono := Real.binEntropy_strictMonoOn.monotoneOn
    (by simpa only [one_div] using ht)
    (by simpa only [one_div] using hupper) (initial_ratio_le hmu)
  have hprod := hm
  rw [actual_totalSize] at hprod
  have hq := (switchIndex_spec (Nat.pos_of_mul_pos_right hprod)
    (actual_depth_condition (n := n) (j := 0) (by omega))
    (actual_residual_pos hm (by omega)) (actual_residual_even n 0)).1
  have hb := (BinomialEntropy.log_choose_entropy_bounds
    (hq.trans (Nat.div_le_self _ _))).2
  change Real.log (queryTerms n 0 : ℝ) ≤
    (residualSize n 0 : ℝ) * Real.binEntropy ((actualSwitch n 0 : ℝ) / residualSize n 0) at hb
  rw [residual_zero] at hb
  have hmul := mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg (α := ℝ) (mu n))
  have hid : (mu n : ℝ) * Real.log 2 * entropy (initialTheta + 1 / (mu n : ℝ)) =
      (mu n : ℝ) * Real.binEntropy (initialTheta + 1 / (mu n : ℝ)) := by
    unfold entropy
    field_simp
  rw [hid]
  exact hb.trans hmul

theorem initial_entropy_tendsto :
    Tendsto (fun n : ℕ => entropy (initialTheta + 1 / (mu n : ℝ))) atTop
      (𝓝 (entropy initialTheta)) := by
  have hu := TrimScales.mu_cast_tendsto_atTop.inv_tendsto_atTop.const_add initialTheta
  simp only [add_zero] at hu
  have hc : Continuous entropy := Real.binEntropy_continuous.div_const _
  simpa only [Function.comp_def, one_div, Pi.inv_apply] using hc.continuousAt.tendsto.comp hu

theorem initial_query_eventually_le_sourceProof {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (queryTerms n 0 : ℝ) ≤
      (n : ℝ) ^ (entropy initialTheta / 5 + d) := by
  have hm := mu_log_ratio_tendsto.const_mul (Real.log 2)
  have hid : Real.log 2 * (1 / (5 * Real.log 2)) = (1 / 5 : ℝ) := by field_simp
  rw [hid] at hm
  have hh := hm.mul initial_entropy_tendsto
  have hrate : Tendsto
      (fun n : ℕ => ((mu n : ℝ) * Real.log 2 * entropy (initialTheta + 1 / (mu n : ℝ))) /
        Real.log n) atTop (𝓝 (entropy initialTheta / 5)) := by
    convert hh using 1
    · funext n
      ring
    · ring
  have hs := hrate.eventually (gt_mem_nhds (by linarith : entropy initialTheta / 5 < entropy initialTheta / 5 + d))
  filter_upwards [hs, TrimScales.mu_tendsto_atTop.eventually (eventually_ge_atTop 50),
    eventually_ge_atTop (2 : ℕ)] with n hn hmu hge
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hb := initial_query_log_bound hmu
  exact Real.le_rpow_of_log_le (by exact_mod_cast (by omega : 0 < n))
    (hb.trans ((div_lt_iff₀ hlog).mp hn).le)












































































end
end ThreeSum.HierarchyScales

end


theorem solution : ∀ {d : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) d →
    @Filter.Eventually.{0} Nat
      (fun (n : Nat) =>
        @LE.le.{0} Real Real.instLE
          (@Nat.cast.{0} Real Real.instNatCast
            (ThreeSum.CostLedger.queryTerms n (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast n)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (ThreeSum.Parameters.entropy ThreeSum.Parameters.initialTheta)
                (@OfNat.ofNat.{0} Real (nat_lit 5)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))
              d)))
      (@Filter.atTop.{0} Nat Nat.instPreorder) := by
  exact @ThreeSum.HierarchyScales.initial_query_eventually_le_sourceProof

#print axioms solution

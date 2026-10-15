-- Prove2me | solution 1 for ThreeSum.Switch.actual_switch_certified
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:42:54.897525+00:00
-- url     : https://prove2.me/submissions/e4b0bcc0-e06c-48a5-854c-969541acdbce

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
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
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_Parameters_phi_le_gamma
import Theorems.Thm_ThreeSum_Parameters_switch_entropy_bound


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales

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











theorem phi_derivative_bound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    phiDeriv t ≤ (889 / 100 : ℝ) := by
  dsimp [phiDeriv]
  have ht2 : t ^ 2 ≤ (1 / 4 : ℝ) := by
    nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  nlinarith [ht.1, ht.2]

theorem phi_derivative_lt_nine {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    phiDeriv t < 9 := lt_of_le_of_lt (phi_derivative_bound ht) (by norm_num)




















































































































theorem hasDerivAt_phi (t : ℝ) : HasDerivAt phi (phiDeriv t) t := by
  have hd := (((hasDerivAt_id t).const_mul (799 / 100)).add
    (((hasDerivAt_id t).pow 2).const_mul (18 / 25))).add
      (((hasDerivAt_id t).pow 3).const_mul (6 / 25))
  change HasDerivAt phi _ t at hd
  apply hd.congr_deriv
  dsimp [phiDeriv]
  ring

theorem phi_increment_bound {u v : ℝ}
    (hu : u ∈ Icc (0 : ℝ) (1 / 2)) (hv : v ∈ Icc (0 : ℝ) (1 / 2)) (huv : u < v) :
    phi v - phi u < 9 * (v - u) := by
  apply (convex_Icc (0 : ℝ) (1 / 2)).image_sub_lt_mul_sub_of_deriv_lt
    (fun y _ => (hasDerivAt_phi y).continuousAt.continuousWithinAt)
    (fun y _ => (hasDerivAt_phi y).differentiableAt.differentiableWithinAt)
    (fun y hy => ?_) u hu v hv huv
  rw [(hasDerivAt_phi y).deriv]
  exact phi_derivative_lt_nine (interior_subset hy)

theorem phi_step_rounding {u v m K : ℝ}
    (hu : u ∈ Icc (0 : ℝ) (1 / 2)) (hv : v ∈ Icc (0 : ℝ) (1 / 2))
    (hm : 0 < m) (hstep : v - u = 1 / m) (hprev : phi u < K) :
    phi v < K + 9 / m := by
  have huv : u < v := by
    have : 0 < 1 / m := by positivity
    linarith
  have h := phi_increment_bound hu hv huv
  rw [hstep] at h
  rw [show 9 / m = 9 * (1 / m) by ring]
  linarith



















































theorem switchThreshold_upper {a : ℝ} (ha : a ∈ Icc (0 : ℝ) terminalFraction) :
    switchThreshold a ≤ 941 / 350 := by
  have hden : 0 < 1 - a := by dsimp [terminalFraction] at ha; linarith [ha.2]
  rw [switchThreshold, div_le_iff₀ hden]
  dsimp [boxSaving, bandShift, terminalFraction] at *
  linarith [ha.2]

theorem switch_box_bound {a t : ℝ} (ha : a ∈ Icc (0 : ℝ) terminalFraction)
    (ht : t ∈ Icc (0 : ℝ) (1 / 2)) (hswitch : switchThreshold a ≤ phi t) :
    boxSaving ≤ 2 * bandShift - a + (1 - a) * gamma t := by
  have hden : 0 < 1 - a := by dsimp [terminalFraction] at ha; linarith [ha.2]
  have hs := (div_le_iff₀ hden).mp hswitch
  have hg := mul_le_mul_of_nonneg_left (phi_le_gamma ht) hden.le
  linarith






































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

theorem switchIndex_pos {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) : 0 < switchIndex J j r := by
  have hs := (switchIndex_spec hJ hj hr heven).2
  by_contra hn
  have hz : switchIndex J j r = 0 := by omega
  rw [hz] at hs
  have hp : 0 < (291 * J + 1000 * j) * r ^ 3 := by positivity
  simp [accepts, cubicNumerator] at hs
  omega

theorem predecessor_rejected {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) :
    ¬ accepts J j r (switchIndex J j r - 1) := by
  have hpos := switchIndex_pos hJ hj hr heven
  have hle := (switchIndex_spec hJ hj hr heven).1
  intro ha
  have hm : switchIndex J j r - 1 ∈ candidates J j r :=
    mem_candidates.mpr ⟨by omega, ha⟩
  have hbad := switchIndex_le hm
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
    (switchIndex J j r : ℝ) / r ∈ Icc (0 : ℝ) (1 / 2) :=
  ratio_mem_half hr (switchIndex_spec hJ hj hr heven).1

theorem phi_enclosure {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) :
    switchThreshold ((j : ℝ) / J) ≤ phi ((switchIndex J j r : ℝ) / r) ∧
      phi ((switchIndex J j r : ℝ) / r) <
        switchThreshold ((j : ℝ) / J) + 9 / r := by
  have hlt := depth_lt hJ hj
  have hspec := switchIndex_spec hJ hj hr heven
  constructor
  · exact (accepts_iff hJ hlt hr).mp hspec.2
  · have hpos := switchIndex_pos hJ hj hr heven
    have hpre : phi (((switchIndex J j r - 1 : ℕ) : ℝ) / r) <
        switchThreshold ((j : ℝ) / J) := by
      apply lt_of_not_ge
      intro ha
      exact predecessor_rejected hJ hj hr heven ((accepts_iff hJ hlt hr).mpr ha)
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    have hpR : ((switchIndex J j r - 1 : ℕ) : ℝ) = (switchIndex J j r : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    apply phi_step_rounding
      (ratio_mem_half hr (show switchIndex J j r - 1 ≤ r / 2 by omega))
      (switch_ratio_mem hJ hj hr heven) hrR ?_ hpre
    rw [hpR]
    field_simp
    <;> ring

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

theorem residual_real_identity {n j : ℕ} (hmu : 0 < mu n)
    (hj : j ≤ terminalDepth n) :
    (residualSize n j : ℝ) =
      (1 - (j : ℝ) / blockCount (inputBits n)) * mu n := by
  have hm := hmu
  rw [actual_totalSize] at hm
  have hp := And.intro (Nat.pos_of_mul_pos_right hm) (Nat.pos_of_mul_pos_left hm)
  have hlt := depth_lt hp.1 (actual_depth_condition hj)
  have hJ : (blockCount (inputBits n) : ℝ) ≠ 0 := by exact_mod_cast hp.1.ne'
  simp only [residualSize, actual_totalSize, Nat.cast_mul, Nat.cast_sub hlt.le]
  field_simp
  <;> ring

theorem actual_switch_certified_sourceProof {n j : ℕ} (hmu : 0 < mu n)
    (hj : j ≤ terminalDepth n) :
    let a : ℝ := (j : ℝ) / blockCount (inputBits n)
    let t : ℝ := (actualSwitch n j : ℝ) / residualSize n j
    t ∈ Icc (0 : ℝ) (1 / 2) ∧
      boxSaving ≤ 2 * bandShift - a + (1 - a) * gamma t ∧
      (1 - a) * entropy t <
        entropyRatio * (1 + boxSaving - 2 * bandShift) + 9 * entropyRatio / mu n := by
  dsimp only
  have hm := hmu
  rw [actual_totalSize] at hm
  have hp := And.intro (Nat.pos_of_mul_pos_right hm) (Nat.pos_of_mul_pos_left hm)
  have hdepth := actual_depth_condition hj
  have hr := actual_residual_pos hmu hj
  have he := actual_residual_even n j
  have ha := depth_fraction hp.1 hdepth
  have ht := switch_ratio_mem hp.1 hdepth hr he
  have hf := phi_enclosure hp.1 hdepth hr he
  change ((switchIndex _ _ _ : ℝ) / _) ∈ _ ∧ _
  refine ⟨ht, switch_box_bound ha ht hf.1, ?_⟩
  apply switch_entropy_bound ha ht (by exact_mod_cast hmu)
  rw [← residual_real_identity hmu hj]
  exact hf.2
















end
end ThreeSum.Switch

end


theorem solution : ∀ {n j : Nat},
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (ThreeSum.Scales.mu n) →
    @LE.le.{0} Nat instLENat j (ThreeSum.Switch.terminalDepth n) →
      have a :=
        @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@Nat.cast.{0} Real Real.instNatCast j)
          (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n)));
      have t :=
        @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.Switch.actualSwitch n j))
          (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.Switch.residualSize n j));
      And
        (@Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
          (@Set.Icc.{0} Real Real.instPreorder
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
          t)
        (And
          (@LE.le.{0} Real Real.instLE ThreeSum.Parameters.boxSaving
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  ThreeSum.Parameters.bandShift)
                a)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) a)
                (ThreeSum.Parameters.gamma t))))
          (@LT.lt.{0} Real Real.instLT
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) a)
              (ThreeSum.Parameters.entropy t))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) ThreeSum.Parameters.entropyRatio
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    ThreeSum.Parameters.boxSaving)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    ThreeSum.Parameters.bandShift)))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 9)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 9) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
                  ThreeSum.Parameters.entropyRatio)
                (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.Scales.mu n)))))) := by
  exact @ThreeSum.Switch.actual_switch_certified_sourceProof

#print axioms solution

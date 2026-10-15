-- Prove2me | solution 1 for ThreeSum.UniformStageBounds.budget_active_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:28:33.436039+00:00
-- url     : https://prove2.me/submissions/f0e54c3c-03e9-4ecd-b53c-a0057f371676

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
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
import Theorems.Thm_ThreeSum_CostLedger_queryTerms_log_bound
import Theorems.Thm_ThreeSum_HierarchyScales_hierarchyEnvelope_log_rate
import Theorems.Thm_ThreeSum_MassScales_falseNumerator_log_rate
import Theorems.Thm_ThreeSum_TrimScales_representationBound_log_rate


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.HierarchyScales
end ThreeSum.HierarchyScales
namespace ThreeSum.MassScales
end ThreeSum.MassScales
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.Switch
end ThreeSum.Switch
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales

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

















































































noncomputable section














































































































theorem muZero_tendsto_atTop : Tendsto muZero atTop atTop :=
  microSize_tendsto_atTop.comp inputBits_tendsto_atTop

theorem muZero_square_log_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => (muZero n : ℝ) ^ 2 / Real.log n) atTop (𝓝 0) := by
  have h := (microSize_square_ratio_tendsto_zero.comp inputBits_tendsto_atTop).mul
    inputBits_log_ratio_tendsto
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [inputBits_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hn0 : (inputBits n : ℝ) ≠ 0 := by exact_mod_cast (by omega : inputBits n ≠ 0)
  simp only [Function.comp_def, muZero]
  field_simp


























































theorem localSearch_log_ratio_tendsto_zero (C : ℕ) :
    Tendsto (fun n : ℕ => Real.log (localSearch C n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have h := muZero_square_log_ratio_tendsto_zero.const_mul ((C : ℝ) * Real.log 2)
  simpa [localSearch, Nat.cast_pow, Nat.cast_mul, Real.log_pow, mul_div_assoc,
    mul_comm, mul_left_comm, mul_assoc] using h

















/-- Converts a proved logarithmic rate into a power bound; the concrete
table and construction functions are instantiated immediately below. -/
theorem eventually_le_rpow_of_log_ratio {f : ℕ → ℕ} {a d : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a))
    (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (n : ℝ) ^ (a + d) := by
  have hs := hf.eventually (gt_mem_nhds (by linarith : a < a + d))
  filter_upwards [hs, eventually_ge_atTop (2 : ℕ)] with n hn hge
  have hnp : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hlog : 0 < Real.log n := Real.log_pos hnp
  exact Real.le_rpow_of_log_le (by linarith) ((div_lt_iff₀ hlog).mp hn).le

theorem localSearch_subpolynomial (C : ℕ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (localSearch C n : ℝ) ≤ (n : ℝ) ^ d := by
  simpa using eventually_le_rpow_of_log_ratio (localSearch_log_ratio_tendsto_zero C) hd

































































































































































































































































































































































































































































































































































































































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





































noncomputable section



































































































































theorem actual_totalSize (n : ℕ) : mu n = blockCount (inputBits n) * muZero n := rfl




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
# Actual finite hierarchy counts

These are the binomial counts used by the concrete microblock hierarchy.
Every prefix partition is included.  The integer switch and its rounding
allowance are applied before any asymptotic estimate is made.  The counts
in this module are combinatorial work counts; the implementation's operation
counts, raw wanted incidences, and false-mass bounds are separate interfaces.
-/

namespace ThreeSum.CostLedger

open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch
open scoped Topology BigOperators

set_option maxHeartbeats 400000






















theorem bandCount_mul_bounds (n : ℕ) :
    n ≤ BandScales.bandSize n * bandCount n ∧
      BandScales.bandSize n * bandCount n < n + BandScales.bandSize n := by
  constructor
  · exact (ceilDiv_le_iff_le_mul (a := BandScales.bandSize n) (b := n)
      (c := bandCount n) (BandScales.bandSize_pos n)).mp le_rfl
  · have h := Nat.div_mul_le_self (n + BandScales.bandSize n - 1) (BandScales.bandSize n)
    simp only [bandCount, Nat.ceilDiv_eq_add_pred_div]
    rw [Nat.mul_comm (BandScales.bandSize n)]
    have hpos := BandScales.bandSize_pos n
    omega
















noncomputable section

















































































































































end
end ThreeSum.CostLedger

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
































theorem terminalDepth_le_mu {n : ℕ} (hmu : 0 < mu n) : terminalDepth n ≤ mu n := by
  have hprod := hmu
  rw [actual_totalSize] at hprod
  have hm := Nat.pos_of_mul_pos_left hprod
  have hc := Nat.mul_le_mul_left (blockCount (inputBits n)) (show 1 ≤ muZero n by omega)
  have hd := actual_depth_condition (n := n) (j := terminalDepth n) le_rfl
  rw [Nat.mul_one, ← actual_totalSize] at hc
  omega

noncomputable section





















theorem allQueryTerms_envelope {n : ℕ} (hmu : 0 < mu n) :
    (allQueryTerms n : ℝ) ≤
      hierarchyEnvelope (entropyRatio * (1 + boxSaving - 2 * bandShift))
        (9 * entropyRatio * Real.log 2) n := by
  unfold allQueryTerms
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ j ∈ Finset.range (terminalDepth n + 1),
        Real.exp ((mu n : ℝ) * Real.log 2 *
          (entropyRatio * (1 + boxSaving - 2 * bandShift)) + 9 * entropyRatio * Real.log 2) := by
      apply Finset.sum_le_sum
      intro j hj
      exact Real.le_exp_of_log_le (queryTerms_log_bound hmu (by simpa using hj))
    _ = (terminalDepth n + 1 : ℝ) *
        Real.exp ((mu n : ℝ) * Real.log 2 *
          (entropyRatio * (1 + boxSaving - 2 * bandShift)) + 9 * entropyRatio * Real.log 2) := by simp
    _ ≤ hierarchyEnvelope (entropyRatio * (1 + boxSaving - 2 * bandShift))
        (9 * entropyRatio * Real.log 2) n := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact_mod_cast Nat.add_le_add_right (terminalDepth_le_mu hmu) 1




























theorem eventually_real_le_rpow_of_log_rate {f : ℕ → ℝ} {a d : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n) / Real.log n) atTop (𝓝 a)) (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, f n ≤ (n : ℝ) ^ (a + d) := by
  have hs := hf.eventually (gt_mem_nhds (by linarith : a < a + d))
  filter_upwards [hs, eventually_ge_atTop (2 : ℕ)] with n hn hge
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  exact Real.le_rpow_of_log_le (by exact_mod_cast (by omega : 0 < n))
    ((div_lt_iff₀ hlog).mp hn).le









theorem allQueryTerms_eventually_le {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (allQueryTerms n : ℝ) ≤
      (n : ℝ) ^ ((entropyRatio * (1 + boxSaving - 2 * bandShift)) / 5 + d) := by
  have he := eventually_real_le_rpow_of_log_rate
    (hierarchyEnvelope_log_rate (entropyRatio * (1 + boxSaving - 2 * bandShift))
      (9 * entropyRatio * Real.log 2)) hd
  filter_upwards [he, TrimScales.mu_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn hmu
  exact (allQueryTerms_envelope (by omega : 0 < mu n)).trans hn












theorem microPartitions_subpolynomial {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (microPartitions n : ℝ) ≤ (n : ℝ) ^ d := by
  filter_upwards [localSearch_subpolynomial 1 hd,
    muZero_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn hmu
  have hpow : muZero n ≤ muZero n ^ 2 := by nlinarith
  have hc : microPartitions n ≤ localSearch 1 n := by
    exact (Nat.choose_le_two_pow _ _).trans (by simpa [localSearch] using Nat.pow_le_pow_right (by norm_num : 0 < 2) hpow)
  exact (show (microPartitions n : ℝ) ≤ localSearch 1 n by exact_mod_cast hc).trans hn






























































































































































end
end ThreeSum.HierarchyScales

end

section


/-!
# Actual wanted-incidence and false-mass majorants

The numerator of the wanted bound retains all raw A occurrences, all three
arithmetic lifts, and every schedule occurrence.  The false bound uses the
actual candidate count, integer band count, score loss, and modulus loss.
No asymptotic premise about an input-dependent mass is assumed here: the
transfer lemmas take the explicit finite inequalities from the counting
and prime-chain algorithms.
-/

namespace ThreeSum.MassScales

open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.CostLedger ThreeSum.HierarchyScales
open scoped Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000












theorem bandCount_pos {n : ℕ} (hn : 0 < n) : 0 < bandCount n :=
  Nat.pos_of_mul_pos_left (hn.trans_le (bandCount_mul_bounds n).1)

theorem rawTripleBound_pos {n : ℕ} (hn : 0 < n) : 0 < rawTripleBound n := by
  have hB := bandCount_pos hn
  have hb := bandSize_pos n
  unfold rawTripleBound
  positivity









theorem scoreLoss_pos (k n : ℕ) : 0 < scoreLoss k n := by
  unfold scoreLoss
  positivity

theorem primeLoss_pos (n : ℕ) : 0 < primeLoss radix n := by
  have hy := primeWindow_ge_two n
  unfold primeLoss
  positivity

theorem candidateCount_eventually_pos : ∀ᶠ n : ℕ in atTop, 0 < candidateCount n := by
  filter_upwards [actual_candidates_nonempty] with n hn
  exact Finset.card_pos.mpr hn

theorem falseNumerator_eventually_pos (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, 0 < falseNumerator k n := by
  filter_upwards [candidateCount_eventually_pos, eventually_ge_atTop (1 : ℕ)] with n hC hn
  have ht := rawTripleBound_pos (by omega : 0 < n)
  have hs := scoreLoss_pos k n
  have hp := primeLoss_pos n
  unfold falseNumerator
  positivity

noncomputable section



















































































































theorem falseMajorant_log_rate (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log (falseMajorant k n) / Real.log n) atTop
      (𝓝 (2 - (1 / 2 - bandShift) / 5)) := by
  have hh := (falseNumerator_log_rate k).sub radix_log_ratio_tendsto
  have hid : (2 + (E + bandShift) / 5) - (E + 1 / 2) / 5 =
      2 - (1 / 2 - bandShift) / 5 := by ring
  rw [hid] at hh
  apply hh.congr'
  filter_upwards [falseNumerator_eventually_pos k] with n hn
  have hN : (falseNumerator k n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hR : (radix n : ℝ) ≠ 0 := by exact_mod_cast (radix_pos n).ne'
  simp only [falseMajorant, Real.log_div hN hR, sub_div]





theorem falseMajorant_eventually_le (k : ℕ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, falseMajorant k n ≤ (n : ℝ) ^ (2 - (1 / 2 - bandShift) / 5 + d) :=
  eventually_real_le_rpow_of_log_rate (falseMajorant_log_rate k) hd






















end
end ThreeSum.MassScales

end

section


/-!
# The six principal finite stage counts

This module assembles actual natural-number work quantities.  Its final
theorem is a runtime-ledger target, not a 3SUM correctness or machine-time
theorem.  The only input-dependent assumptions are four explicit finite
counting inequalities for the wanted mass and the prime-chain score.
An implementation must still connect its operation counter to these counts.
-/

namespace ThreeSum.StageBounds

open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales
open scoped Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000


























noncomputable section





namespace PowerBound

theorem of_rate {f : ℕ → ℕ} {a : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a)) : PowerBound f a :=
  fun _ hd => eventually_le_rpow_of_log_ratio hf hd



theorem mul {f g : ℕ → ℕ} {a b : ℝ} (hf : PowerBound f a) (hg : PowerBound g b) :
    PowerBound (fun n => f n * g n) (a + b) := by
  intro d hd
  filter_upwards [hf (d / 2) (by linarith), hg (d / 2) (by linarith),
    eventually_ge_atTop (1 : ℕ)] with n hfn hgn hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [Nat.cast_mul]
  calc
    _ ≤ (n : ℝ) ^ (a + d / 2) * (n : ℝ) ^ (b + d / 2) :=
      mul_le_mul hfn hgn (Nat.cast_nonneg _) (Real.rpow_nonneg hnR.le _)
    _ = (n : ℝ) ^ ((a + b) + d) := by rw [← Real.rpow_add hnR]; congr 1; ring




























end PowerBound










































































































































































end
end ThreeSum.StageBounds

end

section


/-!
# A uniform size-only budget for the six principal stage counts

Both mass budgets are executable integer divisions of the concrete size
majorants.  The final bound is uniform in the input-dependent masses: the
eventual size threshold is chosen before `W`, `H`, `P`, or `H1` are quantified.
This remains a theorem about the specified finite work quantities, not a
claim that a complete machine has been proved to execute within them.
-/

namespace ThreeSum.UniformStageBounds

open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales ThreeSum.StageBounds
open scoped Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000













noncomputable section













theorem falseBudget_powerBound (k : ℕ) : PowerBound (falseBudget k) (2 - (1 / 2 - bandShift) / 5) := by
  intro d hd
  filter_upwards [falseMajorant_eventually_le k hd] with n hn
  have hb : (falseBudget k n : ℝ) ≤ falseMajorant k n := by
    rw [falseMajorant, le_div_iff₀ (show (0 : ℝ) < radix n by exact_mod_cast radix_pos n)]
    exact_mod_cast Nat.div_mul_le_self (falseNumerator k n) (radix n)
  exact hb.trans hn






theorem budget_active_powerBound_sourceProof (k : ℕ) :
    PowerBound (activeCount (falseBudget k))
      (2 - epsilon * (1 / 2 - bandShift - kappa - entropyRatio * (1 + boxSaving - 2 * bandShift))) := by
  have hG : PowerBound microPartitions 0 := by
    intro d hd
    simpa only [zero_add] using microPartitions_subpolynomial hd
  have hQ : PowerBound allQueryTerms ((entropyRatio * (1 + boxSaving - 2 * bandShift)) / 5) :=
    fun _ hd => allQueryTerms_eventually_le hd
  have hh := (((falseBudget_powerBound k).mul
    (PowerBound.of_rate representationBound_log_rate)).mul hG).mul hQ
  have heq : ((2 - (1 / 2 - bandShift) / 5) + kappa / 5 + 0) +
      (entropyRatio * (1 + boxSaving - 2 * bandShift)) / 5 =
      2 - epsilon * (1 / 2 - bandShift - kappa - entropyRatio * (1 + boxSaving - 2 * bandShift)) := by
    unfold epsilon
    ring
  rw [heq] at hh
  exact hh



















































































end
end ThreeSum.UniformStageBounds

end


theorem solution : ∀ (k : Nat),
  ThreeSum.StageBounds.PowerBound (ThreeSum.StageBounds.activeCount (ThreeSum.UniformStageBounds.falseBudget k))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) ThreeSum.Parameters.epsilon
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
              ThreeSum.Parameters.bandShift)
            ThreeSum.Parameters.kappa)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) ThreeSum.Parameters.entropyRatio
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ThreeSum.Parameters.boxSaving)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                ThreeSum.Parameters.bandShift)))))) := by
  exact @ThreeSum.UniformStageBounds.budget_active_powerBound_sourceProof

#print axioms solution

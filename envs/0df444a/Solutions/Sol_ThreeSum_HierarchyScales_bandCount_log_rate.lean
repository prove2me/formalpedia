-- Prove2me | solution 1 for ThreeSum.HierarchyScales.bandCount_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:04:54.859987+00:00
-- url     : https://prove2.me/submissions/a0feb244-330e-4b45-b830-d86ee1aa5187

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
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
import Theorems.Thm_ThreeSum_BandScales_bandSize_log_rate


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









































noncomputable section







































































































































































































theorem unroundedBandCount_pos {n : ℕ} (hn : 0 < n) : 0 < unroundedBandCount n := by
  exact div_pos (by exact_mod_cast hn) (by exact_mod_cast BandScales.bandSize_pos n)

theorem unroundedBandCount_log_rate :
    Tendsto (fun n : ℕ => Real.log (unroundedBandCount n) / Real.log n) atTop
      (𝓝 (1 - (E + bandShift) / 5)) := by
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hh := hone.sub BandScales.bandSize_log_rate
  change Tendsto (fun n : ℕ => (1 : ℝ) - Real.log (BandScales.bandSize n : ℝ) / Real.log n)
    atTop (𝓝 (1 - (E - 1 / 20) / 5)) at hh
  change Tendsto _ _ (𝓝 (1 - (E - 1 / 20) / 5))
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hbR : (BandScales.bandSize n : ℝ) ≠ 0 := by exact_mod_cast (BandScales.bandSize_pos n).ne'
  have hlog : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
  simp only [unroundedBandCount, Real.log_div hnR hbR, sub_div, div_self hlog]

theorem bandCount_ge_unrounded (n : ℕ) : unroundedBandCount n ≤ (bandCount n : ℝ) := by
  have hb : (0 : ℝ) < BandScales.bandSize n := by exact_mod_cast BandScales.bandSize_pos n
  rw [unroundedBandCount, div_le_iff₀ hb]
  have hn : (n : ℝ) ≤ (BandScales.bandSize n : ℝ) * bandCount n :=
    by exact_mod_cast (bandCount_mul_bounds n).1
  simpa only [mul_comm] using hn

theorem unroundedBandCount_eventually_ge_one :
    ∀ᶠ n : ℕ in atTop, 1 ≤ unroundedBandCount n := by
  have ha : (0 : ℝ) < 1 - (E + bandShift) / 5 := by
    have he := E_bounds.2
    dsimp [bandShift]
    linarith
  have hs := unroundedBandCount_log_rate.eventually (lt_mem_nhds ha)
  filter_upwards [hs, eventually_ge_atTop (2 : ℕ)] with n hn hge
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hb : 0 < Real.log (unroundedBandCount n) := (div_pos_iff.mp hn).elim
    (fun h => h.1) (fun h => False.elim (not_lt_of_ge hlog.le h.2))
  exact ((Real.log_pos_iff (unroundedBandCount_pos (by omega : 0 < n)).le).mp hb).le

theorem bandCount_eventually_le_twice :
    ∀ᶠ n : ℕ in atTop, (bandCount n : ℝ) ≤ 2 * unroundedBandCount n := by
  filter_upwards [unroundedBandCount_eventually_ge_one] with n hn
  have hb : (0 : ℝ) < BandScales.bandSize n := by exact_mod_cast BandScales.bandSize_pos n
  have hu : (BandScales.bandSize n : ℝ) * bandCount n < (n : ℝ) + BandScales.bandSize n :=
    by exact_mod_cast (bandCount_mul_bounds n).2
  have hsmall : (bandCount n : ℝ) < unroundedBandCount n + 1 := by
    rw [unroundedBandCount]
    have hid : (n : ℝ) / BandScales.bandSize n + 1 =
      ((n : ℝ) + BandScales.bandSize n) / BandScales.bandSize n := by field_simp
    rw [hid, lt_div_iff₀ hb]
    simpa only [mul_comm] using hu
  linarith

theorem bandCount_log_rate_sourceProof :
    Tendsto (fun n : ℕ => Real.log (bandCount n : ℝ) / Real.log n) atTop
      (𝓝 (1 - (E + bandShift) / 5)) := by
  have he := Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul (Real.log 2)
  have hh := unroundedBandCount_log_rate.add he
  simp only [mul_zero, add_zero] at hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' unroundedBandCount_log_rate hh
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (unroundedBandCount_pos (by omega)) (bandCount_ge_unrounded n))
      (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
  · filter_upwards [bandCount_eventually_le_twice, eventually_ge_atTop (2 : ℕ)] with n hn hge
    have hp : (0 : ℝ) < bandCount n :=
      lt_of_lt_of_le (unroundedBandCount_pos (by omega)) (bandCount_ge_unrounded n)
    have hlog := Real.log_le_log hp hn
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (unroundedBandCount_pos (by omega : 0 < n)).ne'] at hlog
    have hd := div_le_div_of_nonneg_right hlog
      (show 0 ≤ Real.log (n : ℝ) from Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
    simpa only [add_div, Pi.inv_apply, div_eq_mul_inv, add_mul, add_comm] using hd

end
end ThreeSum.HierarchyScales

end


theorem solution : @Filter.Tendsto.{0, 0} Nat Real
  (fun (n : Nat) =>
    @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (Real.log (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.CostLedger.bandCount n)))
      (Real.log (@Nat.cast.{0} Real Real.instNatCast n)))
  (@Filter.atTop.{0} Nat Nat.instPreorder)
  (@nhds.{0} Real
    (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) ThreeSum.Parameters.E
          ThreeSum.Parameters.bandShift)
        (@OfNat.ofNat.{0} Real (nat_lit 5)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))) := by
  exact @ThreeSum.HierarchyScales.bandCount_log_rate_sourceProof

#print axioms solution

-- Prove2me | solution 1 for ThreeSum.MassScales.falseNumerator_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:15:42.175159+00:00
-- url     : https://prove2.me/submissions/bdf8cd72-421f-4569-90ee-9bf4b4315f7f

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
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
import Theorems.Thm_ThreeSum_HierarchyScales_bandCount_log_rate
import Theorems.Thm_ThreeSum_MassScales_candidateCount_log_rate
import Theorems.Thm_ThreeSum_Scales_primeLoss_log_ratio_tendsto_zero
import Theorems.Thm_ThreeSum_Scales_scoreLoss_log_ratio_tendsto_zero


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.HierarchyScales
end ThreeSum.HierarchyScales
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.Switch
end ThreeSum.Switch
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales

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










noncomputable section





theorem nat_log_rate_const (c : ℕ) :
    Tendsto (fun n : ℕ => Real.log (c : ℝ) / Real.log n) atTop (𝓝 0) := by
  simpa only [mul_zero, Pi.inv_apply, div_eq_mul_inv] using
    Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul (Real.log (c : ℝ))

theorem nat_log_rate_mul {f g : ℕ → ℕ} {a b : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a))
    (hg : Tendsto (fun n : ℕ => Real.log (g n : ℝ) / Real.log n) atTop (𝓝 b))
    (hp : ∀ᶠ n : ℕ in atTop, 0 < f n ∧ 0 < g n) :
    Tendsto (fun n : ℕ => Real.log ((f n * g n : ℕ) : ℝ) / Real.log n) atTop (𝓝 (a + b)) := by
  apply (hf.add hg).congr'
  filter_upwards [hp] with n hn
  have hfR : (f n : ℝ) ≠ 0 := by exact_mod_cast hn.1.ne'
  have hgR : (g n : ℝ) ≠ 0 := by exact_mod_cast hn.2.ne'
  simp only [Nat.cast_mul, Real.log_mul hfR hgR, add_div]

theorem nat_log_rate_pow {f : ℕ → ℕ} {a : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a)) (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log ((f n ^ k : ℕ) : ℝ) / Real.log n) atTop (𝓝 ((k : ℝ) * a)) := by
  simpa only [Nat.cast_pow, Real.log_pow, mul_div_assoc] using hf.const_mul (k : ℝ)

























theorem bandSize_log_rate_shift :
    Tendsto (fun n : ℕ => Real.log (bandSize n : ℝ) / Real.log n) atTop
      (𝓝 ((E + bandShift) / 5)) := by
  simpa only [bandShift, sub_eq_add_neg] using BandScales.bandSize_log_rate





















theorem rawTripleBound_log_rate :
    Tendsto (fun n : ℕ => Real.log (rawTripleBound n : ℝ) / Real.log n) atTop
      (𝓝 (2 + (E + bandShift) / 5)) := by
  have h1 := nat_log_rate_mul (nat_log_rate_const 3) (nat_log_rate_pow bandCount_log_rate 2) (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact ⟨by norm_num, Nat.pow_pos (bandCount_pos (by omega))⟩)
  have h2 := nat_log_rate_mul h1 (nat_log_rate_pow bandSize_log_rate_shift 3) (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact ⟨Nat.mul_pos (by norm_num) (Nat.pow_pos (bandCount_pos (by omega))),
      Nat.pow_pos (bandSize_pos n)⟩)
  convert h2 using 1 <;> simp only [rawTripleBound, Nat.cast_ofNat] <;> ring

theorem falseNumerator_log_rate_sourceProof (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log (falseNumerator k n : ℝ) / Real.log n) atTop
      (𝓝 (2 + (E + bandShift) / 5)) := by
  have h1 := nat_log_rate_mul candidateCount_log_rate rawTripleBound_log_rate (by
    filter_upwards [candidateCount_eventually_pos, eventually_ge_atTop (1 : ℕ)] with n hC hn
    exact ⟨hC, rawTripleBound_pos (by omega)⟩)
  have h2 := nat_log_rate_mul h1 (scoreLoss_log_ratio_tendsto_zero k) (by
    filter_upwards [candidateCount_eventually_pos, eventually_ge_atTop (1 : ℕ)] with n hC hn
    exact ⟨Nat.mul_pos hC (rawTripleBound_pos (by omega)), scoreLoss_pos k n⟩)
  have h3 := nat_log_rate_mul h2 primeLoss_log_ratio_tendsto_zero (by
    filter_upwards [candidateCount_eventually_pos, eventually_ge_atTop (1 : ℕ)] with n hC hn
    exact ⟨Nat.mul_pos (Nat.mul_pos hC (rawTripleBound_pos (by omega))) (scoreLoss_pos k n),
      primeLoss_pos n⟩)
  simpa only [falseNumerator, zero_add, add_zero] using h3
























































end
end ThreeSum.MassScales

end


theorem solution : ∀ (k : Nat),
  @Filter.Tendsto.{0, 0} Nat Real
    (fun (n : Nat) =>
      @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (Real.log (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.MassScales.falseNumerator k n)))
        (Real.log (@Nat.cast.{0} Real Real.instNatCast n)))
    (@Filter.atTop.{0} Nat Nat.instPreorder)
    (@nhds.{0} Real
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) ThreeSum.Parameters.E
            ThreeSum.Parameters.bandShift)
          (@OfNat.ofNat.{0} Real (nat_lit 5)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))) := by
  exact @ThreeSum.MassScales.falseNumerator_log_rate_sourceProof

#print axioms solution

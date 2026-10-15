-- Prove2me | solution 1 for ThreeSum.StageBounds.terminalChoices_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:30:52.062159+00:00
-- url     : https://prove2.me/submissions/253f19ca-1b1c-4a1a-8e1d-29484f836bba

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
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
import Theorems.Thm_ThreeSum_Switch_terminal_fraction_exact


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
namespace ThreeSum.Switch
end ThreeSum.Switch
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales

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











theorem depth_lt {J j : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J) : j < J := by
  omega






















































































































theorem actual_totalSize (n : ℕ) : mu n = blockCount (inputBits n) * muZero n := rfl




theorem actual_depth_condition {n j : ℕ} (hj : j ≤ terminalDepth n) :
    20 * j ≤ 13 * blockCount (inputBits n) := by
  have hm := Nat.div_mul_le_self (13 * blockCount (inputBits n)) 20
  unfold terminalDepth at hj
  omega








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








































end
end ThreeSum.Switch

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














































end PowerBound











































































theorem terminalChoices_log_rate_sourceProof :
    Tendsto (fun n : ℕ => Real.log (terminalChoices n : ℝ) / Real.log n) atTop
      (𝓝 ((1 - terminalFraction) / 5)) := by
  have hh := mu_log_ratio_tendsto.const_mul (Real.log 2 * (1 - terminalFraction))
  have heq : Real.log 2 * (1 - terminalFraction) * (1 / (5 * Real.log 2)) =
      (1 - terminalFraction) / 5 := by field_simp
  rw [heq] at hh
  apply hh.congr'
  filter_upwards [mu_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hid := residual_real_identity (by omega : 0 < mu n)
    (j := terminalDepth n) le_rfl
  rw [terminal_fraction_exact (by omega : 0 < mu n)] at hid
  simp only [terminalChoices, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, hid]
  ring

















































































end
end ThreeSum.StageBounds

end


theorem solution : @Filter.Tendsto.{0, 0} Nat Real
  (fun (n : Nat) =>
    @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (Real.log (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.StageBounds.terminalChoices n)))
      (Real.log (@Nat.cast.{0} Real Real.instNatCast n)))
  (@Filter.atTop.{0} Nat Nat.instPreorder)
  (@nhds.{0} Real
    (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ThreeSum.Parameters.terminalFraction)
      (@OfNat.ofNat.{0} Real (nat_lit 5)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))) := by
  exact @ThreeSum.StageBounds.terminalChoices_log_rate_sourceProof

#print axioms solution

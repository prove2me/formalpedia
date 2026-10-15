-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.TrimScales.representationBound_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:11:48.92933+00:00
-- url     : https://prove2.me/submissions/57c20031-3df4-4e54-b237-9cb58c7a0b3f

import Aesop
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_TrimScales_localLength_log_rate
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_TrimScales_replicatedHalf_log_rate

local instance platformRadixNonzero_9f25426a6c (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Filter
end Filter
namespace Finset
end Finset
namespace Real
end Real
namespace Set
end Set
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BinomialEntropy
end ThreeSum.BinomialEntropy
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BinomialEntropy
end ThreeSum1960614.Machine.ThreeSum.BinomialEntropy
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales

namespace ThreeSum1960614.Machine

/-!
# Finite numerical bounds for the local cover

The graph degree bound follows from exact finite cardinalities: the degree
is no larger than the number of vertices, while vertices times degree equal
outputs times representations per output.  This avoids any approximation
of factorials.  The prime-interval and normalized first-moment estimates
are stated explicitly in terms of the concrete binomial coefficients.
-/

namespace ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LocalCoverBounds


open scoped _root_.BigOperators


































/-! ## A deterministic selected prime -/































/-! ## Exact integer rounding of the separable bucket cap -/



theorem bucketCap_formula (V p : ℕ) :
    _root_.ThreeSum.LocalCoverBounds.bucketCap V p = (4 * (p + V) + p - 1) / p := rfl

theorem bucketCap_le_iff {V p b : ℕ} (hp : 0 < p) :
    _root_.ThreeSum.LocalCoverBounds.bucketCap V p ≤ b ↔ 4 * (p + V) ≤ b * p := by
  simpa only [_root_.ThreeSum.LocalCoverBounds.bucketCap, Nat.mul_comm] using
    (ceilDiv_le_iff_le_mul (b := 4 * (p + V)) (c := b) hp)

theorem bucketCap_threshold {V p : ℕ} (hp : 0 < p) :
    4 * (p + V) ≤ _root_.ThreeSum.LocalCoverBounds.bucketCap V p * p :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.bucketCap_le_iff hp).mp le_rfl

theorem bucketCap_mul_lt {V p : ℕ} (hp : 0 < p) :
    _root_.ThreeSum.LocalCoverBounds.bucketCap V p * p < 4 * (p + V) + p := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.bucketCap_formula]
  have hdiv := Nat.div_mul_le_self (4 * (p + V) + p - 1) p
  omega

theorem bucketCap_real_bound {V p : ℕ} (hp : 0 < p) :
    (_root_.ThreeSum.LocalCoverBounds.bucketCap V p : ℝ) < 5 + 4 * (V : ℝ) / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hb : (_root_.ThreeSum.LocalCoverBounds.bucketCap V p : ℝ) * p < 4 * (p + (V : ℝ)) + p := by
    exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.bucketCap_mul_lt (V := V) hp
  rw [show 5 + 4 * (V : ℝ) / p = (5 * p + 4 * V) / p by field_simp,
    lt_div_iff₀ hp0]
  nlinarith

/-! ## The actual local parameters at `L=464*h` -/

































theorem localBucketCap_threshold (h : ℕ) :
    4 * (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h + _root_.ThreeSum.LocalCoverBounds.vertexCount (464 * h) h) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h * _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.bucketCap_threshold (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h)

end ThreeSum.LocalCoverBounds

end ThreeSum1960614.Machine

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


























theorem kappa_positive : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.kappa := by
  obtain ⟨_,_,hl,_⟩ := _root_.ThreeSum1960614.Machine.ThreeSum1960614.encoding_parameter_bounds
  have hk : _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.kappa = _root_.ThreeSum1960614.kappa 232 := by
    norm_num [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.kappa,_root_.ThreeSum.Parameters.entropy,_root_.ThreeSum1960614.kappa,_root_.ThreeSum1960614.entropy]
  rw [hk]
  linarith







































end ThreeSum.Parameters

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A finite entropy certificate for every binomial coefficient

The proof uses the mode of the exact binomial expansion with integral weights `k`
and `n-k`. It does not invoke Stirling's formula or introduce an asymptotic assumption.
-/

noncomputable section

namespace ThreeSum.BinomialEntropy
open _root_.ThreeSum.BinomialEntropy


open _root_.Finset
open _root_.Real
open _root_.Set
open _root_.Filter
open scoped _root_.Topology

set_option maxRecDepth 10000





































/-- The actual local vertex count, with `mu=2h`, has the multiplicity rate used by the cover. -/
theorem vertex_table_rate :
    Tendsto (fun h : ℕ => Real.log ((464 * h).choose h : ℝ) / ((2 * h : ℝ) * Real.log 2))
      atTop (𝓝 (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + 1 / 2 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.kappa / 2)) := by
  have h := (_root_.ThreeSum.BinomialEntropy.fixed_ratio_bits_tendsto (c := 464) (r := 1) (by norm_num) (by norm_num)).div_const 2
  convert h using 1
  · funext m
    simp only [Nat.one_mul, div_div]
    congr 1
    ring
  · norm_num [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E, _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.kappa]
    ring



end ThreeSum.BinomialEntropy

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual vertex and trimmed-bucket scales

The local prime and bucket cap are the computable finite selections from
`LocalCoverBounds`.  Their logarithmic rates are derived from those exact
definitions and the exact integer schedule in `Scales`.
-/

namespace ThreeSum.TrimScales
open _root_.ThreeSum.TrimScales


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open scoped _root_.Topology

















noncomputable section







theorem vertexLoad_pos (h : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.vertexLoad h := by
  have hV : (0 : ℝ) < _root_.ThreeSum.LocalCoverBounds.vertexCount (464 * h) h := by
    exact_mod_cast (Nat.choose_pos (by omega : h ≤ 464 * h))
  have hp : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h := by
    exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h
  exact div_pos hV hp

theorem vertexLoad_log_rate :
    Tendsto (fun h : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.vertexLoad h) / ((2 * h : ℝ) * Real.log 2))
      atTop (𝓝 (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.kappa / 2)) := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.BinomialEntropy.vertex_table_rate.sub _root_.ThreeSum1960614.Machine.ThreeSum.Scales.localPrime_log_rate
  have heq : (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + 1 / 2 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.kappa / 2) - (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + 1 / 2) =
      _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.kappa / 2 := by ring
  rw [heq] at h
  apply h.congr'
  filter_upwards [] with h
  have hV : (0 : ℝ) < _root_.ThreeSum.LocalCoverBounds.vertexCount (464 * h) h := by
    exact_mod_cast (Nat.choose_pos (by omega : h ≤ 464 * h))
  have hp : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h := by
    exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.vertexLoad, Real.log_div hV.ne' hp.ne', sub_div]
  rfl

theorem vertexLoad_eventually_ge_one : ∀ᶠ h : ℕ in atTop, 1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.vertexLoad h := by
  have hpos : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.kappa / 2 := by have := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.kappa_positive; linarith
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.vertexLoad_log_rate.eventually (lt_mem_nhds hpos)
  filter_upwards [hr, eventually_ge_atTop (1 : ℕ)] with h hh hhpos
  have hhp : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have hden : 0 < (2 * h : ℝ) * Real.log 2 := by positivity
  have hlog : 0 < Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.vertexLoad h) := (div_pos_iff.mp hh).elim
    (fun hp => hp.1) (fun hp => False.elim (not_lt_of_ge hden.le hp.2))
  exact (Real.log_pos_iff (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.vertexLoad_pos h).le).mp hlog |>.le

theorem localBucketCap_ge_load (h : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.vertexLoad h ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h : ℝ) := by
  have hp : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h := by
    exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h
  have hV : (0 : ℝ) ≤ _root_.ThreeSum.LocalCoverBounds.vertexCount (464 * h) h := Nat.cast_nonneg _
  have ht : 4 * (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h +
      (_root_.ThreeSum.LocalCoverBounds.vertexCount (464 * h) h : ℝ)) ≤
      (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h : ℝ) * _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h := by
    exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap_threshold h
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.vertexLoad, div_le_iff₀ hp]
  nlinarith

theorem localBucketCap_pos (h : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h := by
  have h := (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.vertexLoad_pos h).trans_le (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localBucketCap_ge_load h)
  exact_mod_cast h

theorem localBucketCap_eventually_le_nine_load :
    ∀ᶠ h : ℕ in atTop, (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h : ℝ) ≤ 9 * _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.vertexLoad h := by
  filter_upwards [_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.vertexLoad_eventually_ge_one] with h hh
  have hu := _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.bucketCap_real_bound (V := _root_.ThreeSum.LocalCoverBounds.vertexCount (464 * h) h)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h)
  change (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h : ℝ) <
    5 + 4 * (_root_.ThreeSum.LocalCoverBounds.vertexCount (464 * h) h : ℝ) / _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h at hu
  change (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h : ℝ) ≤
    9 * ((_root_.ThreeSum.LocalCoverBounds.vertexCount (464 * h) h : ℝ) / _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)
  change 1 ≤ (_root_.ThreeSum.LocalCoverBounds.vertexCount (464 * h) h : ℝ) / _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h at hh
  rw [mul_div_assoc] at hu
  linarith

theorem localBucketCap_log_rate :
    Tendsto (fun h : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h : ℝ) /
      ((2 * h : ℝ) * Real.log 2)) atTop (𝓝 (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.kappa / 2)) := by
  have herr : Tendsto (fun h : ℕ => Real.log 9 / ((2 * h : ℝ) * Real.log 2))
      atTop (𝓝 0) := by
    have hi := (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hi.const_mul (Real.log 9 / (2 * Real.log 2))
  have hu := _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.vertexLoad_log_rate.add herr
  simp only [add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.vertexLoad_log_rate hu
  · filter_upwards [] with h
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.vertexLoad_pos h) (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localBucketCap_ge_load h)) (by positivity)
  · filter_upwards [_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localBucketCap_eventually_le_nine_load] with h hh
    have hc : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h := by exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localBucketCap_pos h
    have hlog := Real.log_le_log hc hh
    rw [Real.log_mul (by norm_num : (9 : ℝ) ≠ 0) (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.vertexLoad_pos h).ne'] at hlog
    have hd := div_le_div_of_nonneg_right hlog (by positivity :
      (0 : ℝ) ≤ (2 * h : ℝ) * Real.log 2)
    simpa only [add_div, add_comm] using hd

theorem trimMultiplicity_log_rate :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.trimMultiplicity n : ℝ) / Real.log n) atTop
      (𝓝 (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.kappa)) := by
  have h := (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.replicatedHalf_log_rate _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localBucketCap_log_rate).const_mul 2
  have heq : 2 * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.kappa / 2)) = _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.kappa := by ring
  rw [heq] at h
  convert h using 1
  funext n
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.trimMultiplicity, _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.replicatedHalf, Nat.cast_pow, Real.log_pow, Nat.cast_mul, Nat.cast_ofNat]
  ring







theorem localLength_pos (h : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength h := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength, _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localSchedule_length]
  positivity





theorem scheduleCount_log_rate :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n : ℝ) / Real.log n) atTop (𝓝 0) := by
  simpa [_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount] using _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.replicatedHalf_log_rate _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength_log_rate

theorem representationBound_eq (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.representationBound n = _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n * _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.trimMultiplicity n := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.representationBound, _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount, _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.replicatedHalf, _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.trimMultiplicity, mul_pow, pow_mul]



















end

end ThreeSum.TrimScales

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales

open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open scoped _root_.Topology
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales

section

theorem ThreeSum1960614.Machine.ThreeSum.TrimScales.representationBound_log_rate__implementation_2c5e40538e :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.representationBound n : ℝ) / Real.log n) atTop
      (𝓝 (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.kappa)) := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount_log_rate.add _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.trimMultiplicity_log_rate
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [] with n
  have hs : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n := by
    exact_mod_cast (Nat.pow_pos (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength_pos (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n))) :
      0 < _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n)
  have ht : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.trimMultiplicity n := by
    exact_mod_cast (Nat.pow_pos (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localBucketCap_pos (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n))) :
      0 < _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.trimMultiplicity n)
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.representationBound_eq, Nat.cast_mul, Real.log_mul hs.ne' ht.ne', add_div]
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.TrimScales.representationBound_log_rate__implementation_2c5e40538e) := (@ThreeSum1960614.Machine.ThreeSum.TrimScales.representationBound_log_rate__implementation_2c5e40538e)

#print axioms solution

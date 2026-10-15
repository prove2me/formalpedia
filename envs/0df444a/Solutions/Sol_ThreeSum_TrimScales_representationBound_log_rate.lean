-- Prove2me | solution 1 for ThreeSum.TrimScales.representationBound_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:43:42.370662+00:00
-- url     : https://prove2.me/submissions/9f32425f-e605-45c2-98e2-cb4dd01a353c

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
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
import Theorems.Thm_ThreeSum_Parameters_kappa_positive
import Theorems.Thm_ThreeSum_TrimScales_localLength_log_rate
import Theorems.Thm_ThreeSum_TrimScales_replicatedHalf_log_rate


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.Scales
end ThreeSum.Scales

section


/-!
# A finite entropy certificate for every binomial coefficient

The proof uses the mode of the exact binomial expansion with integral weights `k`
and `n-k`. It does not invoke Stirling's formula or introduce an asymptotic assumption.
-/

noncomputable section

namespace ThreeSum.BinomialEntropy

open Finset Real Set Filter
open scoped Topology

set_option maxRecDepth 10000










































































































































































































































/-- The actual local vertex count, with `mu=2h`, has the multiplicity rate used by the cover. -/
theorem vertex_table_rate :
    Tendsto (fun h : ℕ => Real.log ((512 * h).choose h : ℝ) / ((2 * h : ℝ) * Real.log 2))
      atTop (𝓝 (ThreeSum.Parameters.E + 1 / 2 + ThreeSum.Parameters.kappa / 2)) := by
  have h := (fixed_ratio_bits_tendsto (c := 512) (r := 1) (by norm_num) (by norm_num)).div_const 2
  convert h using 1
  · funext m
    simp only [Nat.one_mul, div_div]
    congr 1
    ring
  · norm_num [ThreeSum.Parameters.E, ThreeSum.Parameters.kappa]
    ring














end ThreeSum.BinomialEntropy

end
end

section


/-!
# Finite numerical bounds for the local cover

The graph degree bound follows from exact finite cardinalities: the degree
is no larger than the number of vertices, while vertices times degree equal
outputs times representations per output.  This avoids any approximation
of factorials.  The prime-interval and normalized first-moment estimates
are stated explicitly in terms of the concrete binomial coefficients.
-/

namespace ThreeSum.LocalCoverBounds

open scoped BigOperators



































































































































/-! ## A deterministic selected prime -/















































































/-! ## Exact integer rounding of the separable bucket cap -/




theorem bucketCap_formula (V p : ℕ) :
    bucketCap V p = (4 * (p + V) + p - 1) / p := rfl

theorem bucketCap_le_iff {V p b : ℕ} (hp : 0 < p) :
    bucketCap V p ≤ b ↔ 4 * (p + V) ≤ b * p := by
  simpa only [bucketCap, Nat.mul_comm] using
    (ceilDiv_le_iff_le_mul (b := 4 * (p + V)) (c := b) hp)

theorem bucketCap_threshold {V p : ℕ} (hp : 0 < p) :
    4 * (p + V) ≤ bucketCap V p * p :=
  (bucketCap_le_iff hp).mp le_rfl

theorem bucketCap_mul_lt {V p : ℕ} (hp : 0 < p) :
    bucketCap V p * p < 4 * (p + V) + p := by
  rw [bucketCap_formula]
  have hdiv := Nat.div_mul_le_self (4 * (p + V) + p - 1) p
  omega

theorem bucketCap_real_bound {V p : ℕ} (hp : 0 < p) :
    (bucketCap V p : ℝ) < 5 + 4 * (V : ℝ) / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hb : (bucketCap V p : ℝ) * p < 4 * (p + (V : ℝ)) + p := by
    exact_mod_cast bucketCap_mul_lt (V := V) hp
  rw [show 5 + 4 * (V : ℝ) / p = (5 * p + 4 * V) / p by field_simp,
    lt_div_iff₀ hp0]
  nlinarith

/-! ## The actual local parameters at `L=512*h` -/

























































theorem localBucketCap_threshold (h : ℕ) :
    4 * (localPrime h + vertexCount (512 * h) h) ≤ localBucketCap h * localPrime h :=
  bucketCap_threshold (localPrime_pos h)

end ThreeSum.LocalCoverBounds

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






























theorem vertexLoad_pos (h : ℕ) : 0 < vertexLoad h := by
  have hV : (0 : ℝ) < LocalCoverBounds.vertexCount (512 * h) h := by
    exact_mod_cast (Nat.choose_pos (by omega : h ≤ 512 * h))
  have hp : (0 : ℝ) < LocalCoverBounds.localPrime h := by
    exact_mod_cast LocalCoverBounds.localPrime_pos h
  exact div_pos hV hp

theorem vertexLoad_log_rate :
    Tendsto (fun h : ℕ => Real.log (vertexLoad h) / ((2 * h : ℝ) * Real.log 2))
      atTop (𝓝 (Parameters.kappa / 2)) := by
  have h := BinomialEntropy.vertex_table_rate.sub localPrime_log_rate
  have heq : (Parameters.E + 1 / 2 + Parameters.kappa / 2) - (Parameters.E + 1 / 2) =
      Parameters.kappa / 2 := by ring
  rw [heq] at h
  apply h.congr'
  filter_upwards [] with h
  have hV : (0 : ℝ) < LocalCoverBounds.vertexCount (512 * h) h := by
    exact_mod_cast (Nat.choose_pos (by omega : h ≤ 512 * h))
  have hp : (0 : ℝ) < LocalCoverBounds.localPrime h := by
    exact_mod_cast LocalCoverBounds.localPrime_pos h
  rw [vertexLoad, Real.log_div hV.ne' hp.ne', sub_div]
  rfl

theorem vertexLoad_eventually_ge_one : ∀ᶠ h : ℕ in atTop, 1 ≤ vertexLoad h := by
  have hpos : 0 < Parameters.kappa / 2 := by have := Parameters.kappa_positive; linarith
  have hr := vertexLoad_log_rate.eventually (lt_mem_nhds hpos)
  filter_upwards [hr, eventually_ge_atTop (1 : ℕ)] with h hh hhpos
  have hhp : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have hden : 0 < (2 * h : ℝ) * Real.log 2 := by positivity
  have hlog : 0 < Real.log (vertexLoad h) := (div_pos_iff.mp hh).elim
    (fun hp => hp.1) (fun hp => False.elim (not_lt_of_ge hden.le hp.2))
  exact (Real.log_pos_iff (vertexLoad_pos h).le).mp hlog |>.le

theorem localBucketCap_ge_load (h : ℕ) :
    vertexLoad h ≤ (LocalCoverBounds.localBucketCap h : ℝ) := by
  have hp : (0 : ℝ) < LocalCoverBounds.localPrime h := by
    exact_mod_cast LocalCoverBounds.localPrime_pos h
  have hV : (0 : ℝ) ≤ LocalCoverBounds.vertexCount (512 * h) h := Nat.cast_nonneg _
  have ht : 4 * (LocalCoverBounds.localPrime h +
      (LocalCoverBounds.vertexCount (512 * h) h : ℝ)) ≤
      (LocalCoverBounds.localBucketCap h : ℝ) * LocalCoverBounds.localPrime h := by
    exact_mod_cast LocalCoverBounds.localBucketCap_threshold h
  rw [vertexLoad, div_le_iff₀ hp]
  nlinarith

theorem localBucketCap_pos (h : ℕ) : 0 < LocalCoverBounds.localBucketCap h := by
  have h := (vertexLoad_pos h).trans_le (localBucketCap_ge_load h)
  exact_mod_cast h

theorem localBucketCap_eventually_le_nine_load :
    ∀ᶠ h : ℕ in atTop, (LocalCoverBounds.localBucketCap h : ℝ) ≤ 9 * vertexLoad h := by
  filter_upwards [vertexLoad_eventually_ge_one] with h hh
  have hu := LocalCoverBounds.bucketCap_real_bound (V := LocalCoverBounds.vertexCount (512 * h) h)
    (LocalCoverBounds.localPrime_pos h)
  change (LocalCoverBounds.localBucketCap h : ℝ) <
    5 + 4 * (LocalCoverBounds.vertexCount (512 * h) h : ℝ) / LocalCoverBounds.localPrime h at hu
  change (LocalCoverBounds.localBucketCap h : ℝ) ≤
    9 * ((LocalCoverBounds.vertexCount (512 * h) h : ℝ) / LocalCoverBounds.localPrime h)
  change 1 ≤ (LocalCoverBounds.vertexCount (512 * h) h : ℝ) / LocalCoverBounds.localPrime h at hh
  rw [mul_div_assoc] at hu
  linarith

theorem localBucketCap_log_rate :
    Tendsto (fun h : ℕ => Real.log (LocalCoverBounds.localBucketCap h : ℝ) /
      ((2 * h : ℝ) * Real.log 2)) atTop (𝓝 (Parameters.kappa / 2)) := by
  have herr : Tendsto (fun h : ℕ => Real.log 9 / ((2 * h : ℝ) * Real.log 2))
      atTop (𝓝 0) := by
    have hi := (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hi.const_mul (Real.log 9 / (2 * Real.log 2))
  have hu := vertexLoad_log_rate.add herr
  simp only [add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' vertexLoad_log_rate hu
  · filter_upwards [] with h
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (vertexLoad_pos h) (localBucketCap_ge_load h)) (by positivity)
  · filter_upwards [localBucketCap_eventually_le_nine_load] with h hh
    have hc : (0 : ℝ) < LocalCoverBounds.localBucketCap h := by exact_mod_cast localBucketCap_pos h
    have hlog := Real.log_le_log hc hh
    rw [Real.log_mul (by norm_num : (9 : ℝ) ≠ 0) (vertexLoad_pos h).ne'] at hlog
    have hd := div_le_div_of_nonneg_right hlog (by positivity :
      (0 : ℝ) ≤ (2 * h : ℝ) * Real.log 2)
    simpa only [add_div, add_comm] using hd

theorem trimMultiplicity_log_rate :
    Tendsto (fun n : ℕ => Real.log (trimMultiplicity n : ℝ) / Real.log n) atTop
      (𝓝 (Parameters.kappa / 5)) := by
  have h := (replicatedHalf_log_rate localBucketCap_log_rate).const_mul 2
  have heq : 2 * (Parameters.kappa / 2 / 5) = Parameters.kappa / 5 := by ring
  rw [heq] at h
  convert h using 1
  funext n
  simp only [trimMultiplicity, replicatedHalf, Nat.cast_pow, Real.log_pow, Nat.cast_mul, Nat.cast_ofNat]
  ring

























theorem localLength_pos (h : ℕ) : 0 < localLength h := by
  simp only [localLength, LocalHashMoments.localSchedule_length]
  positivity


































theorem scheduleCount_log_rate :
    Tendsto (fun n : ℕ => Real.log (scheduleCount n : ℝ) / Real.log n) atTop (𝓝 0) := by
  simpa [scheduleCount] using replicatedHalf_log_rate localLength_log_rate

theorem representationBound_eq (n : ℕ) :
    representationBound n = scheduleCount n * trimMultiplicity n := by
  simp only [representationBound, scheduleCount, replicatedHalf, trimMultiplicity, mul_pow, pow_mul]

theorem representationBound_log_rate_sourceProof :
    Tendsto (fun n : ℕ => Real.log (representationBound n : ℝ) / Real.log n) atTop
      (𝓝 (Parameters.kappa / 5)) := by
  have h := scheduleCount_log_rate.add trimMultiplicity_log_rate
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [] with n
  have hs : (0 : ℝ) < scheduleCount n := by
    exact_mod_cast (Nat.pow_pos (localLength_pos (microHalf (inputBits n))) :
      0 < scheduleCount n)
  have ht : (0 : ℝ) < trimMultiplicity n := by
    exact_mod_cast (Nat.pow_pos (localBucketCap_pos (microHalf (inputBits n))) :
      0 < trimMultiplicity n)
  rw [representationBound_eq, Nat.cast_mul, Real.log_mul hs.ne' ht.ne', add_div]


















































































end

end ThreeSum.TrimScales

end


theorem solution : @Filter.Tendsto.{0, 0} Nat Real
  (fun (n : Nat) =>
    @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (Real.log (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.TrimScales.representationBound n)))
      (Real.log (@Nat.cast.{0} Real Real.instNatCast n)))
  (@Filter.atTop.{0} Nat Nat.instPreorder)
  (@nhds.{0} Real
    (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      ThreeSum.Parameters.kappa
      (@OfNat.ofNat.{0} Real (nat_lit 5)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))) := by
  exact @ThreeSum.TrimScales.representationBound_log_rate_sourceProof

#print axioms solution

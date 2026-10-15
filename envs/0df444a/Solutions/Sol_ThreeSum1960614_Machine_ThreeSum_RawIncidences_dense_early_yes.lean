-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.RawIncidences.dense_early_yes
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:01:08.752087+00:00
-- url     : https://prove2.me/submissions/85324620-1816-4ef6-b93c-bb63e76ba2aa

import Aesop
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle08
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.OfFn
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
import Mathlib.RingTheory.Coprime.Lemmas
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
import Theorems.Thm_ThreeSum_Arithmetic_early_yes
import Theorems.Thm_ThreeSum_LocalHashMoments_hitCount_cap
import Theorems.Thm_ThreeSum_Radix_mem_representations
import Theorems.Thm_ThreeSum_Radix_representations_card_le

namespace Finset
end Finset
namespace ThreeSum
end ThreeSum
namespace ThreeSum.Arithmetic
end ThreeSum.Arithmetic
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.Arithmetic
end ThreeSum1960614.Machine.ThreeSum.Arithmetic
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences

namespace ThreeSum1960614.Machine

/-!
# Exact arithmetic interface for the deterministic histogram construction

These are finite arithmetic and counting theorems.  They do not assert a
running-time bound or the existence of a word-RAM implementation.
-/

namespace ThreeSum.Arithmetic
open _root_.ThreeSum.Arithmetic


open _root_.Finset
open scoped _root_.BigOperators

/-! ## Guarded arithmetic-to-radix lifts -/

/-- A multiple of a positive modulus strictly between its two nearest
nonzero multiples must vanish. -/
theorem eq_zero_of_dvd_of_bounds {R x : ℤ} (hR : 0 < R)
    (hlo : -R < x) (hhi : x < R) (hdiv : R ∣ x) : x = 0 := by
  obtain ⟨q, rfl⟩ := hdiv
  by_cases hq : q = 0
  · simp [hq]
  have hcases : q ≤ -1 ∨ 1 ≤ q := by omega
  rcases hcases with hq | hq
  · have hm := mul_le_mul_of_nonneg_left hq hR.le
    nlinarith
  · have hm := mul_le_mul_of_nonneg_left hq hR.le
    nlinarith



/-- With the range guard, a radix congruence for a normalized input triple
is an integer equality with one of the three arithmetic lifts. -/
theorem guarded_lift_eq {P R a b c d j : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ R)
    (ha0 : 0 ≤ a) (haP : a < P)
    (hb0 : 0 ≤ b) (hbP : b < P)
    (hc0 : 0 ≤ c) (hcP : c < P)
    (hj : _root_.ThreeSum.Arithmetic.SmallLift j)
    (hcong : R ∣ (c + d - b) - (a + j * P + d)) :
    c - b = a + j * P := by
  have hR : 0 < R := by omega
  have hdiv : R ∣ c - b - a - j * P := by
    convert hcong using 1 <;> ring
  have hbds : -R < c - b - a - j * P ∧ c - b - a - j * P < R := by
    rcases hj with rfl | rfl | rfl <;> constructor <;> nlinarith
  have hz := _root_.ThreeSum1960614.Machine.ThreeSum.Arithmetic.eq_zero_of_dvd_of_bounds hR hbds.1 hbds.2 hdiv
  linarith

/-- A queried representation cannot introduce an alias that fails the
arithmetic congruence. -/
theorem arithmetic_dvd_of_guarded_lift {P R a b c d j : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ R)
    (ha0 : 0 ≤ a) (haP : a < P)
    (hb0 : 0 ≤ b) (hbP : b < P)
    (hc0 : 0 ≤ c) (hcP : c < P)
    (hj : _root_.ThreeSum.Arithmetic.SmallLift j)
    (hcong : R ∣ (c + d - b) - (a + j * P + d)) :
    P ∣ c - b - a := by
  have heq := _root_.ThreeSum1960614.Machine.ThreeSum.Arithmetic.guarded_lift_eq hP hguard ha0 haP hb0 hbP hc0 hcP hj hcong
  refine ⟨j, ?_⟩
  nlinarith

/-- Distinct signed lifts of a fixed A residue never give the same radix
query key under the range guard. -/
theorem guarded_lift_unique {P R a d j k : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ R)
    (hj : _root_.ThreeSum.Arithmetic.SmallLift j) (hk : _root_.ThreeSum.Arithmetic.SmallLift k)
    (hcong : R ∣ (a + j * P + d) - (a + k * P + d)) : j = k := by
  have hR : 0 < R := by omega
  have hdiv : R ∣ (j - k) * P := by
    convert hcong using 1 <;> ring
  have hbds : -R < (j - k) * P ∧ (j - k) * P < R := by
    rcases hj with rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl <;> constructor <;> nlinarith
  have hz := _root_.ThreeSum1960614.Machine.ThreeSum.Arithmetic.eq_zero_of_dvd_of_bounds hR hbds.1 hbds.2 hdiv
  rcases mul_eq_zero.mp hz with h | h
  · omega
  · omega



/-- Guarded radix-key equality implies the arithmetic divisibility test on
the original signed integer values, not only on their canonical residues. -/
theorem guarded_remainder_lift_sound {P R a b c d j : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ R) (hj : _root_.ThreeSum.Arithmetic.SmallLift j)
    (hkey : Int.ModEq R (a % P + j * P + d) (c % P + d - b % P)) :
    P ∣ c - b - a := by
  have hp0 : P ≠ 0 := ne_of_gt hP
  have hnorm : P ∣ c % P - b % P - a % P :=
    _root_.ThreeSum1960614.Machine.ThreeSum.Arithmetic.arithmetic_dvd_of_guarded_lift hP hguard
      (Int.emod_nonneg _ hp0) (Int.emod_lt_of_pos _ hP)
      (Int.emod_nonneg _ hp0) (Int.emod_lt_of_pos _ hP)
      (Int.emod_nonneg _ hp0) (Int.emod_lt_of_pos _ hP) hj hkey.dvd
  have heq : Int.ModEq P (c % P - b % P - a % P) (c - b - a) :=
    ((Int.mod_modEq c P).sub (Int.mod_modEq b P)).sub (Int.mod_modEq a P)
  exact Int.modEq_zero_iff_dvd.mp (heq.symm.trans hnorm.modEq_zero_int)



/-! ## The weighted false-count identity -/



















theorem missWeight_pos_of_witness {L : Finset ℤ} {x l : ℤ}
    (hl : l ∈ L) (hnot : ¬ l ∣ x) : 1 ≤ _root_.ThreeSum.Arithmetic.missWeight L x := by
  have h := Finset.single_le_sum (s := L)
    (f := fun z : ℤ => if z ∣ x then (0 : ℕ) else 1)
    (fun z hz => Nat.zero_le _) hl
  simpa [_root_.ThreeSum.Arithmetic.missWeight, hnot] using h





/-- Auxiliary tests separating every nonzero input difference make the
weighted score an upper bound on the number of false modular triples. -/
theorem falseCount_le_weightedFalseCount {ι : Type*} (T : Finset ι)
    (difference : ι → ℤ) (L : Finset ℤ) (m : ℤ)
    (hsep : ∀ i ∈ T, difference i ≠ 0 → ∃ l ∈ L, ¬ l ∣ difference i) :
    (∑ i ∈ T, if m ∣ difference i ∧ difference i ≠ 0 then (1 : ℕ) else 0) ≤
      _root_.ThreeSum.Arithmetic.weightedFalseCount T difference L m := by
  unfold _root_.ThreeSum.Arithmetic.weightedFalseCount
  apply Finset.sum_le_sum
  intro i hi
  by_cases h : m ∣ difference i ∧ difference i ≠ 0
  · obtain ⟨l, hl, hnot⟩ := hsep i hi h.2
    simpa [h, h.1] using _root_.ThreeSum1960614.Machine.ThreeSum.Arithmetic.missWeight_pos_of_witness hl hnot
  · simp only [if_neg h]
    exact Nat.zero_le _

/-! ## Exact early YES from per-original-triple representation caps -/







end ThreeSum.Arithmetic

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual local one-hot covers

This module instantiates the hash moment and separable trimming proofs with
the disjoint-subset graph. The sample space consists of all assignments to
the two actual symbols at every coordinate. The resulting deterministic
greedy schedule covers every ordered field target, including equal targets.
-/

namespace ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalHashMoments


open _root_.Finset
open scoped _root_.BigOperators

open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {L h : ℕ}















































/-! ## The selected local prime and its actual finite schedule -/

















theorem local_representation_cap (h : ℕ) (w : _root_.ThreeSum.LocalHashMoments.Weight (464 * h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h))
    (target : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h × _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) :
    _root_.ThreeSum.LocalHashMoments.hitCount (464 * h) h (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h) w target ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h ^ 2 :=
  _root_.ThreeSum.LocalHashMoments.hitCount_cap _ _ _



end ThreeSum.LocalHashMoments

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Concrete retained choices and the global radix encoding

The local choice type retains the occurrence of a map in the deterministic
schedule.  Repeated chosen maps therefore keep their representation
multiplicity.  Canonical integer lifts of their one-hot coefficients feed
the radix recursion, whose coverage and cap are instantiated here with no
local-cover assumptions.
-/

namespace ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalEncoding


set_option maxRecDepth 8000

open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments






















theorem retained_survives {h : ℕ} (c : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h) :
    _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Survives h (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence c) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge c) := c.property



theorem rawHash_cast {h L : ℕ} (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) (s : Fin L → Bool) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash w s : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) = _root_.ThreeSum.HashFamily.hashValue w s := by
  simp [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash, _root_.ThreeSum.HashFamily.hashValue]





theorem dvd_sub_rawHash_iff {h L : ℕ} (a : ℤ)
    (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) (s : Fin L → Bool) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ) ∣ a - _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash w s ↔
      _root_.ThreeSum.HashFamily.hashValue w s = (a : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash_cast, sub_eq_zero]
  exact eq_comm





theorem mem_localFiber {h : ℕ} (a b : ℤ) (c : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h) :
    c ∈ _root_.ThreeSum.Radix.localFiber (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight a b ↔
      _root_.ThreeSum.HashFamily.hashValue (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence c)) (_root_.ThreeSum.LocalGraph.left (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge c)) = (a : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) ∧
      _root_.ThreeSum.HashFamily.hashValue (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence c)) (_root_.ThreeSum.LocalGraph.right (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge c)) = (b : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) := by
  simp only [_root_.ThreeSum.Radix.localFiber, Finset.mem_filter, Finset.mem_univ, true_and,
    _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft, _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight, _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.dvd_sub_rawHash_iff]



section

set_option maxHeartbeats 1000000 in
private theorem private_6c1c69abb9_occurrence_fiber_bound (h : ℕ) (a b : ℤ) (i : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h) :
    ((_root_.ThreeSum.Radix.localFiber (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight a b : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h)).filter
      (fun c => _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence c = i)).card ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h ^ 2 := by
  let hits : Finset (_root_.ThreeSum.LocalGraph.Edge (464 * h) h) := Finset.univ.filter fun e =>
    _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h i ∈ _root_.ThreeSum.HashFamily.trimmedPairEvent (_root_.ThreeSum.LocalGraph.left e) (_root_.ThreeSum.LocalGraph.right e)
      (a : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) (b : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)
      (_root_.ThreeSum.LocalGraph.leftVertices (464 * h) h) (_root_.ThreeSum.LocalGraph.rightVertices (464 * h) h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h)
  have hcount : ((_root_.ThreeSum.Radix.localFiber (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight a b :
      Finset (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h)).filter (fun c => _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence c = i)).card ≤ hits.card := by
    apply Finset.card_le_card_of_injOn _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge
    · intro c hc
      obtain ⟨hc, hi⟩ := Finset.mem_filter.mp hc
      obtain ⟨ha, hb⟩ := (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mem_localFiber a b c).mp hc
      simp only [hi] at ha hb
      have hs := _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.retained_survives c
      simp only [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Survives, hi, ha, hb] at hs
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, hs⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by simpa only [hi] using And.intro ha hb⟩
    · intro c hc d hd he
      apply Subtype.ext
      apply Prod.ext
      · exact (Finset.mem_filter.mp hc).2.trans (Finset.mem_filter.mp hd).2.symm
      · exact he
  exact hcount.trans (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.local_representation_cap h (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h i) (a, b))
end


/-- The exact local cap counts map occurrences separately, including
repetitions in the chosen greedy schedule. -/
theorem localFiber_card_bound (h : ℕ) (a b : ℤ) :
    (_root_.ThreeSum.Radix.localFiber (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight a b : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h)).card ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h * _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h ^ 2 := by
  calc
    _ = ∑ i : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h,
        ((_root_.ThreeSum.Radix.localFiber (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight a b : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h)).filter
          (fun c => _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence c = i)).card := by
      exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ ≤ ∑ _i : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h, _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.private_6c1c69abb9_occurrence_fiber_bound h a b i
    _ = _ := by simp [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence]







theorem mem_representations (h J : ℕ) (a b : ℤ) (xs : List (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h)) :
    xs ∈ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representations h J a b ↔ xs.length = J ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ a - _root_.ThreeSum.Radix.positionalHash (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft xs ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ b - _root_.ThreeSum.Radix.positionalHash (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight xs := by
  exact _root_.ThreeSum.Radix.mem_representations (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)
    (by exact_mod_cast (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h).ne') _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight J a b xs



theorem representations_card_bound (h J : ℕ) (a b : ℤ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representations h J a b).card ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J :=
  _root_.ThreeSum.Radix.representations_card_le (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight
    (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h * _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h ^ 2) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.localFiber_card_bound h) J a b





theorem rawHash_difference {h L k : ℕ} (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h))
    (e : _root_.ThreeSum.LocalGraph.Edge L k) :
    _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash w (_root_.ThreeSum.LocalGraph.right e) - _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash w (_root_.ThreeSum.LocalGraph.left e) = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawOutput w (_root_.ThreeSum.LocalGraph.output e) := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawOutput
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hd := Finset.disjoint_left.mp (_root_.ThreeSum.LocalGraph.edge_data e).2.2
  by_cases hs : i ∈ e.val.1 <;> by_cases hv : i ∈ e.val.2 <;>
    simp_all [_root_.ThreeSum.LocalGraph.left, _root_.ThreeSum.LocalGraph.right, _root_.ThreeSum.LocalGraph.leftWord, _root_.ThreeSum.LocalGraph.rightWord, _root_.ThreeSum.LocalGraph.output]







theorem blockKey_choice {h : ℕ} (c : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h) :
    _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.blockKey (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.blockOfChoice c) = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight c - _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft c :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash_difference (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence c)) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge c)).symm









theorem positionalHash_difference {h : ℕ} (xs : List (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h)) :
    _root_.ThreeSum.Radix.positionalHash (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight xs -
      _root_.ThreeSum.Radix.positionalHash (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft xs =
        _root_.ThreeSum.Radix.positionalHash (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.blockKey (xs.map _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.blockOfChoice) := by
  induction xs with
  | nil => simp [_root_.ThreeSum.Radix.positionalHash]
  | cons c xs ih =>
      simp only [List.map_cons, _root_.ThreeSum.Radix.positionalHash, _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.blockKey_choice]
      rw [← ih]
      ring











end ThreeSum.GlobalEncoding

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original-index incidences in the guarded global encoding

An incidence retains its original input indices, its complete sequence of
chosen-map occurrences and retained local edges, and its signed arithmetic
lift. Equal input values remain distinct original indices. The lift is
unique for a fixed original triple and representation, so it does not add
a factor of three to the representation bound.
-/

namespace ThreeSum.RawIncidences
open _root_.ThreeSum.RawIncidences


set_option maxRecDepth 8000

open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds



theorem lift_small (j : Fin 3) : _root_.ThreeSum.Arithmetic.SmallLift (_root_.ThreeSum.RawIncidences.lift j) := by
  fin_cases j <;> simp [_root_.ThreeSum.RawIncidences.lift, _root_.ThreeSum.Arithmetic.SmallLift]

theorem lift_injective : Function.Injective _root_.ThreeSum.RawIncidences.lift := by
  intro i j hij
  apply Fin.ext
  unfold _root_.ThreeSum.RawIncidences.lift at hij
  omega

















theorem tupleKey_eq {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleKey t = _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleRight t - _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleLeft t := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleKey, _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey, _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleRight, _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleLeft, _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.positionalHash_difference]
  congr 1
  exact List.map_ofFn.symm















theorem tuple_mem_representations {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) (b c : ℤ) :
    List.ofFn t ∈ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representations h J b c ↔
      _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ b - _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleLeft t ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ c - _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleRight t := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mem_representations]
  simp only [List.length_ofFn, true_and, _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleLeft, _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleRight]

theorem tuple_difference_congruence {h J : ℕ} {t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J} {b c : ℤ}
    (ht : List.ofFn t ∈ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representations h J b c) :
    _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ (c - b) - _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleKey t := by
  obtain ⟨hb, hc⟩ := (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tuple_mem_representations t b c).mp ht
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleKey_eq]
  rw [sub_sub_sub_comm]
  exact dvd_sub hc hb







theorem mem_witnesses {h J : ℕ} {P d a b c : ℤ} {w : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.Witness h J} :
    w ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witnesses h J P d a b c ↔
      List.ofFn w.1 ∈ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representations h J (b % P) (c % P + d) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ (a % P + _root_.ThreeSum.RawIncidences.lift w.2 * P + d) - _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleKey w.1 := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witnesses, Finset.mem_filter, Finset.mem_univ, true_and]

theorem witness_sound {h J : ℕ} {P d a b c : ℤ} {w : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.Witness h J}
    (hP : 0 < P) (hguard : 4 * P ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J)
    (hw : w ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witnesses h J P d a b c) : P ∣ c - b - a := by
  obtain ⟨hrep, hquery⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.mem_witnesses.mp hw
  have hdiff := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tuple_difference_congruence hrep
  have hkey : Int.ModEq (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J)
      (a % P + _root_.ThreeSum.RawIncidences.lift w.2 * P + d) (c % P + d - b % P) := by
    apply Int.modEq_of_dvd
    simpa only [sub_sub_sub_cancel_right] using dvd_sub hdiff hquery
  exact _root_.ThreeSum1960614.Machine.ThreeSum.Arithmetic.guarded_remainder_lift_sound hP hguard (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.lift_small w.2) hkey





/-- Projection to the retained list is injective on the raw witnesses of
one original triple: the guard makes its lift unique. -/
theorem witness_projection_injective {h J : ℕ} {P d a b c : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J) :
    Set.InjOn (fun w : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.Witness h J => List.ofFn w.1) (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witnesses h J P d a b c) := by
  intro w hw v hv he
  have ht : w.1 = v.1 := List.ofFn_injective he
  have hwq := (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.mem_witnesses.mp hw).2
  have hvq := (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.mem_witnesses.mp hv).2
  have hd : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣
      (a % P + _root_.ThreeSum.RawIncidences.lift w.2 * P + d) - (a % P + _root_.ThreeSum.RawIncidences.lift v.2 * P + d) := by
    rw [ht] at hwq
    simpa only [sub_sub_sub_cancel_right] using dvd_sub hwq hvq
  have hj := _root_.ThreeSum1960614.Machine.ThreeSum.Arithmetic.guarded_lift_unique hP hguard (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.lift_small w.2) (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.lift_small v.2) hd
  exact Prod.ext ht (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.lift_injective hj)

theorem witnesses_card_bound {h J : ℕ} {P d a b c : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witnesses h J P d a b c).card ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J := by
  calc
    _ ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representations h J (b % P) (c % P + d)).card := by
      apply Finset.card_le_card_of_injOn (fun w : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.Witness h J => List.ofFn w.1)
      · intro w hw
        exact (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.mem_witnesses.mp hw).1
      · exact _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witness_projection_injective hP hguard
    _ ≤ _ := _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representations_card_bound h J (b % P) (c % P + d)





section OriginalIndices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]









theorem mem_rawOn {h J : ℕ} {P d : ℤ} {T : Finset (_root_.ThreeSum.RawIncidences.Original α β γ)}
    {a : α → ℤ} {b : β → ℤ} {c : γ → ℤ} {r : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ} :
    r ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P d T a b c ↔
      r.1 ∈ T ∧ r.2 ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witnesses h J P d (a r.1.1) (b r.1.2.1) (c r.1.2.2) :=
  Finset.mem_sigma

theorem raw_sound {h J : ℕ} {P d : ℤ} {T : Finset (_root_.ThreeSum.RawIncidences.Original α β γ)}
    {a : α → ℤ} {b : β → ℤ} {c : γ → ℤ} {r : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ}
    (hP : 0 < P) (hguard : 4 * P ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J)
    (hr : r ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P d T a b c) : P ∣ _root_.ThreeSum.RawIncidences.difference a b c r.1 :=
  _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witness_sound hP hguard (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.mem_rawOn.mp hr).2





theorem raw_owner_fiber_bound {h J : ℕ} {P d : ℤ} (T : Finset (_root_.ThreeSum.RawIncidences.Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ)
    (hP : 0 < P) (hguard : 4 * P ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J) (t : _root_.ThreeSum.RawIncidences.Original α β γ) :
    ((_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P d T a b c).filter fun r => r.1 = t).card ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J := by
  calc
    _ ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witnesses h J P d (a t.1) (b t.2.1) (c t.2.2)).card := by
      apply Finset.card_le_card_of_injOn (fun r : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ => r.2)
      · intro r hr
        obtain ⟨hr, ht⟩ := Finset.mem_filter.mp hr
        have hw := (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.mem_rawOn.mp hr).2
        simpa only [Finset.mem_coe, ht] using hw
      · intro r hr s hs he
        have hrt := (Finset.mem_filter.mp hr).2
        have hst := (Finset.mem_filter.mp hs).2
        exact Sigma.ext (hrt.trans hst.symm) (heq_of_eq he)
    _ ≤ _ := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witnesses_card_bound hP hguard

theorem raw_owner_weight_bound {h J : ℕ} {P d : ℤ} (T : Finset (_root_.ThreeSum.RawIncidences.Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ)
    (hP : 0 < P) (hguard : 4 * P ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J) (t : _root_.ThreeSum.RawIncidences.Original α β γ) :
    _root_.ThreeSum.Arithmetic.fiberWeight (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P d T a b c) Sigma.fst (fun _ => 1) t ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J := by
  have he : _root_.ThreeSum.Arithmetic.fiberWeight (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P d T a b c) Sigma.fst (fun _ => 1) t =
      ((_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P d T a b c).filter fun r => r.1 = t).card := by
    simp only [_root_.ThreeSum.Arithmetic.fiberWeight, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [he]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.raw_owner_fiber_bound T a b c hP hguard t



























end OriginalIndices

end ThreeSum.RawIncidences

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences

set_option maxRecDepth 8000
open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
section

/-- The dense stopping rule uses the actual guarded incidences and the
actual radix multiplicity bound. Its score is the weighted false-count
quantity computed by the arithmetic histogram identities. -/
theorem ThreeSum1960614.Machine.ThreeSum.RawIncidences.dense_early_yes__implementation_1b0861e9dc {h J : ℕ} {P d : ℤ} (T : Finset (_root_.ThreeSum.RawIncidences.Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (aux : Finset ℤ)
    (hP : 0 < P) (hguard : 4 * P ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J)
    (hsep : ∀ t ∈ T, _root_.ThreeSum.RawIncidences.difference a b c t ≠ 0 → ∃ l ∈ aux, ¬l ∣ _root_.ThreeSum.RawIncidences.difference a b c t)
    (hlarge : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J * _root_.ThreeSum.Arithmetic.weightedFalseCount T (_root_.ThreeSum.RawIncidences.difference a b c) aux P <
      _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawMass h J P d T a b c) :
    ∃ t ∈ T, _root_.ThreeSum.RawIncidences.difference a b c t = 0 := by
  let good : _root_.ThreeSum.RawIncidences.Original α β γ → Prop :=
    fun t => t ∉ T ∨ ¬P ∣ _root_.ThreeSum.RawIncidences.difference a b c t ∨ _root_.ThreeSum.RawIncidences.difference a b c t = 0
  have hset : (Finset.univ.filter fun t : _root_.ThreeSum.RawIncidences.Original α β γ => ¬good t) =
      T.filter (fun t => P ∣ _root_.ThreeSum.RawIncidences.difference a b c t ∧ _root_.ThreeSum.RawIncidences.difference a b c t ≠ 0) := by
    ext t
    simp [good]
  have hcount : (Finset.univ.filter fun t : _root_.ThreeSum.RawIncidences.Original α β γ => ¬good t).card ≤
      _root_.ThreeSum.Arithmetic.weightedFalseCount T (_root_.ThreeSum.RawIncidences.difference a b c) aux P := by
    rw [hset, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact _root_.ThreeSum1960614.Machine.ThreeSum.Arithmetic.falseCount_le_weightedFalseCount T (_root_.ThreeSum.RawIncidences.difference a b c) aux P hsep
  have hmass : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J * _root_.ThreeSum.Arithmetic.weightedFalseCount T (_root_.ThreeSum.RawIncidences.difference a b c) aux P <
      ∑ _r ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P d T a b c, (1 : ℕ) := by
    simpa only [Finset.sum_const, smul_eq_mul, mul_one, _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawMass] using hlarge
  obtain ⟨r, hr, _, hg⟩ := _root_.ThreeSum.Arithmetic.early_yes
    (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P d T a b c) Sigma.fst (fun _ => 1) good
    (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J) (_root_.ThreeSum.Arithmetic.weightedFalseCount T (_root_.ThreeSum.RawIncidences.difference a b c) aux P)
    (fun t _ => _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.raw_owner_weight_bound T a b c hP hguard t) hcount hmass
  have ht := (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.mem_rawOn.mp hr).1
  have hd := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.raw_sound hP hguard hr
  refine ⟨r.1, ht, ?_⟩
  rcases hg with hnot | hnot | hz
  · exact False.elim (hnot ht)
  · exact False.elim (hnot hd)
  · exact hz
end

end

theorem solution.{u_implementation_0,u_implementation_1,u_implementation_2} : type_of% (@ThreeSum1960614.Machine.ThreeSum.RawIncidences.dense_early_yes__implementation_1b0861e9dc.{u_implementation_0,u_implementation_1,u_implementation_2}) := (@ThreeSum1960614.Machine.ThreeSum.RawIncidences.dense_early_yes__implementation_1b0861e9dc.{u_implementation_0,u_implementation_1,u_implementation_2})

#print axioms solution

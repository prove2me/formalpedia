-- Prove2me | solution 1 for ThreeSum.RawIncidences.dense_early_yes
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:42:55.605367+00:00
-- url     : https://prove2.me/submissions/73636671-0fd9-4fbb-a90f-dbc036bea667

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments

section


/-!
# Exact arithmetic interface for the deterministic histogram construction

These are finite arithmetic and counting theorems.  They do not assert a
running-time bound or the existence of a word-RAM implementation.
-/

namespace ThreeSum.Arithmetic

open Finset
open scoped BigOperators

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
    (hj : SmallLift j)
    (hcong : R ∣ (c + d - b) - (a + j * P + d)) :
    c - b = a + j * P := by
  have hR : 0 < R := by omega
  have hdiv : R ∣ c - b - a - j * P := by
    convert hcong using 1 <;> ring
  have hbds : -R < c - b - a - j * P ∧ c - b - a - j * P < R := by
    rcases hj with rfl | rfl | rfl <;> constructor <;> nlinarith
  have hz := eq_zero_of_dvd_of_bounds hR hbds.1 hbds.2 hdiv
  linarith

/-- A queried representation cannot introduce an alias that fails the
arithmetic congruence. -/
theorem arithmetic_dvd_of_guarded_lift {P R a b c d j : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ R)
    (ha0 : 0 ≤ a) (haP : a < P)
    (hb0 : 0 ≤ b) (hbP : b < P)
    (hc0 : 0 ≤ c) (hcP : c < P)
    (hj : SmallLift j)
    (hcong : R ∣ (c + d - b) - (a + j * P + d)) :
    P ∣ c - b - a := by
  have heq := guarded_lift_eq hP hguard ha0 haP hb0 hbP hc0 hcP hj hcong
  refine ⟨j, ?_⟩
  nlinarith

/-- Distinct signed lifts of a fixed A residue never give the same radix
query key under the range guard. -/
theorem guarded_lift_unique {P R a d j k : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ R)
    (hj : SmallLift j) (hk : SmallLift k)
    (hcong : R ∣ (a + j * P + d) - (a + k * P + d)) : j = k := by
  have hR : 0 < R := by omega
  have hdiv : R ∣ (j - k) * P := by
    convert hcong using 1 <;> ring
  have hbds : -R < (j - k) * P ∧ (j - k) * P < R := by
    rcases hj with rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl <;> constructor <;> nlinarith
  have hz := eq_zero_of_dvd_of_bounds hR hbds.1 hbds.2 hdiv
  rcases mul_eq_zero.mp hz with h | h
  · omega
  · omega












/-- Guarded radix-key equality implies the arithmetic divisibility test on
the original signed integer values, not only on their canonical residues. -/
theorem guarded_remainder_lift_sound {P R a b c d j : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ R) (hj : SmallLift j)
    (hkey : Int.ModEq R (a % P + j * P + d) (c % P + d - b % P)) :
    P ∣ c - b - a := by
  have hp0 : P ≠ 0 := ne_of_gt hP
  have hnorm : P ∣ c % P - b % P - a % P :=
    arithmetic_dvd_of_guarded_lift hP hguard
      (Int.emod_nonneg _ hp0) (Int.emod_lt_of_pos _ hP)
      (Int.emod_nonneg _ hp0) (Int.emod_lt_of_pos _ hP)
      (Int.emod_nonneg _ hp0) (Int.emod_lt_of_pos _ hP) hj hkey.dvd
  have heq : Int.ModEq P (c % P - b % P - a % P) (c - b - a) :=
    ((Int.mod_modEq c P).sub (Int.mod_modEq b P)).sub (Int.mod_modEq a P)
  exact Int.modEq_zero_iff_dvd.mp (heq.symm.trans hnorm.modEq_zero_int)

























/-! ## The weighted false-count identity -/








































































































theorem missWeight_pos_of_witness {L : Finset ℤ} {x l : ℤ}
    (hl : l ∈ L) (hnot : ¬ l ∣ x) : 1 ≤ missWeight L x := by
  have h := Finset.single_le_sum (s := L)
    (f := fun z : ℤ => if z ∣ x then (0 : ℕ) else 1)
    (fun z hz => Nat.zero_le _) hl
  simpa [missWeight, hnot] using h

















/-- Auxiliary tests separating every nonzero input difference make the
weighted score an upper bound on the number of false modular triples. -/
theorem falseCount_le_weightedFalseCount {ι : Type*} (T : Finset ι)
    (difference : ι → ℤ) (L : Finset ℤ) (m : ℤ)
    (hsep : ∀ i ∈ T, difference i ≠ 0 → ∃ l ∈ L, ¬ l ∣ difference i) :
    (∑ i ∈ T, if m ∣ difference i ∧ difference i ≠ 0 then (1 : ℕ) else 0) ≤
      weightedFalseCount T difference L m := by
  unfold weightedFalseCount
  apply Finset.sum_le_sum
  intro i hi
  by_cases h : m ∣ difference i ∧ difference i ≠ 0
  · obtain ⟨l, hl, hnot⟩ := hsep i hi h.2
    simpa [h, h.1] using missWeight_pos_of_witness hl hnot
  · simp only [if_neg h]
    exact Nat.zero_le _

/-! ## Exact early YES from per-original-triple representation caps -/



































































end ThreeSum.Arithmetic

end

section


/-!
# Actual local one-hot covers

This module instantiates the hash moment and separable trimming proofs with
the disjoint-subset graph. The sample space consists of all assignments to
the two actual symbols at every coordinate. The resulting deterministic
greedy schedule covers every ordered field target, including equal targets.
-/

namespace ThreeSum.LocalHashMoments

open Finset
open scoped BigOperators

open LocalGraph LocalCoverBounds

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {L h : ℕ}














































































































































































































































/-! ## The selected local prime and its actual finite schedule -/














































theorem local_representation_cap (h : ℕ) (w : Weight (512 * h) (LocalField h))
    (target : LocalField h × LocalField h) :
    hitCount (512 * h) h (localBucketCap h) w target ≤ localBucketCap h ^ 2 :=
  hitCount_cap _ _ _


















end ThreeSum.LocalHashMoments

end

section


/-!
# Concrete retained choices and the global radix encoding

The local choice type retains the occurrence of a map in the deterministic
schedule.  Repeated chosen maps therefore keep their representation
multiplicity.  Canonical integer lifts of their one-hot coefficients feed
the radix recursion, whose coverage and cap are instantiated here with no
local-cover assumptions.
-/

namespace ThreeSum.GlobalEncoding

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments






































theorem retained_survives {h : ℕ} (c : RetainedChoice h) :
    Survives h (occurrence c) (edge c) := c.property






theorem rawHash_cast {h L : ℕ} (w : Weight L (LocalField h)) (s : Fin L → Bool) :
    (rawHash w s : LocalField h) = HashFamily.hashValue w s := by
  simp [rawHash, HashFamily.hashValue]
















theorem dvd_sub_rawHash_iff {h L : ℕ} (a : ℤ)
    (w : Weight L (LocalField h)) (s : Fin L → Bool) :
    (localPrime h : ℤ) ∣ a - rawHash w s ↔
      HashFamily.hashValue w s = (a : LocalField h) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, rawHash_cast, sub_eq_zero]
  exact eq_comm







theorem mem_localFiber {h : ℕ} (a b : ℤ) (c : RetainedChoice h) :
    c ∈ Radix.localFiber (localPrime h) rawLeft rawRight a b ↔
      HashFamily.hashValue (mapAt h (occurrence c)) (left (edge c)) = (a : LocalField h) ∧
      HashFamily.hashValue (mapAt h (occurrence c)) (right (edge c)) = (b : LocalField h) := by
  simp only [Radix.localFiber, Finset.mem_filter, Finset.mem_univ, true_and,
    rawLeft, rawRight, dvd_sub_rawHash_iff]
















set_option maxHeartbeats 1000000 in
private theorem occurrence_fiber_bound (h : ℕ) (a b : ℤ) (i : Occurrence h) :
    ((Radix.localFiber (localPrime h) rawLeft rawRight a b : Finset (RetainedChoice h)).filter
      (fun c => occurrence c = i)).card ≤ localBucketCap h ^ 2 := by
  let hits : Finset (Edge (512 * h) h) := Finset.univ.filter fun e =>
    mapAt h i ∈ HashFamily.trimmedPairEvent (left e) (right e)
      (a : LocalField h) (b : LocalField h)
      (leftVertices (512 * h) h) (rightVertices (512 * h) h) (localBucketCap h)
  have hcount : ((Radix.localFiber (localPrime h) rawLeft rawRight a b :
      Finset (RetainedChoice h)).filter (fun c => occurrence c = i)).card ≤ hits.card := by
    apply Finset.card_le_card_of_injOn edge
    · intro c hc
      obtain ⟨hc, hi⟩ := Finset.mem_filter.mp hc
      obtain ⟨ha, hb⟩ := (mem_localFiber a b c).mp hc
      simp only [hi] at ha hb
      have hs := retained_survives c
      simp only [Survives, hi, ha, hb] at hs
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
  exact hcount.trans (local_representation_cap h (mapAt h i) (a, b))

/-- The exact local cap counts map occurrences separately, including
repetitions in the chosen greedy schedule. -/
theorem localFiber_card_bound (h : ℕ) (a b : ℤ) :
    (Radix.localFiber (localPrime h) rawLeft rawRight a b : Finset (RetainedChoice h)).card ≤
      scheduleSize h * localBucketCap h ^ 2 := by
  calc
    _ = ∑ i : Occurrence h,
        ((Radix.localFiber (localPrime h) rawLeft rawRight a b : Finset (RetainedChoice h)).filter
          (fun c => occurrence c = i)).card := by
      exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ ≤ ∑ _i : Occurrence h, localBucketCap h ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact occurrence_fiber_bound h a b i
    _ = _ := by simp [Occurrence]









theorem mem_representations (h J : ℕ) (a b : ℤ) (xs : List (RetainedChoice h)) :
    xs ∈ representations h J a b ↔ xs.length = J ∧
      globalModulus h J ∣ a - Radix.positionalHash (localPrime h) rawLeft xs ∧
      globalModulus h J ∣ b - Radix.positionalHash (localPrime h) rawRight xs := by
  exact Radix.mem_representations (localPrime h)
    (by exact_mod_cast (localPrime_pos h).ne') rawLeft rawRight J a b xs






theorem representations_card_bound (h J : ℕ) (a b : ℤ) :
    (representations h J a b).card ≤ representationCap h J :=
  Radix.representations_card_le (localPrime h) rawLeft rawRight
    (scheduleSize h * localBucketCap h ^ 2) (localFiber_card_bound h) J a b

















theorem rawHash_difference {h L k : ℕ} (w : Weight L (LocalField h))
    (e : Edge L k) :
    rawHash w (right e) - rawHash w (left e) = rawOutput w (output e) := by
  unfold rawHash rawOutput
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hd := Finset.disjoint_left.mp (edge_data e).2.2
  by_cases hs : i ∈ e.val.1 <;> by_cases hv : i ∈ e.val.2 <;>
    simp_all [left, right, leftWord, rightWord, output]











theorem blockKey_choice {h : ℕ} (c : RetainedChoice h) :
    blockKey (blockOfChoice c) = rawRight c - rawLeft c :=
  (rawHash_difference (mapAt h (occurrence c)) (edge c)).symm
















theorem positionalHash_difference {h : ℕ} (xs : List (RetainedChoice h)) :
    Radix.positionalHash (localPrime h) rawRight xs -
      Radix.positionalHash (localPrime h) rawLeft xs =
        Radix.positionalHash (localPrime h) blockKey (xs.map blockOfChoice) := by
  induction xs with
  | nil => simp [Radix.positionalHash]
  | cons c xs ih =>
      simp only [List.map_cons, Radix.positionalHash, blockKey_choice]
      rw [← ih]
      ring















































end ThreeSum.GlobalEncoding

end

section


/-!
# Original-index incidences in the guarded global encoding

An incidence retains its original input indices, its complete sequence of
chosen-map occurrences and retained local edges, and its signed arithmetic
lift. Equal input values remain distinct original indices. The lift is
unique for a fixed original triple and representation, so it does not add
a factor of three to the representation bound.
-/

namespace ThreeSum.RawIncidences

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds



theorem lift_small (j : Fin 3) : Arithmetic.SmallLift (lift j) := by
  fin_cases j <;> simp [lift, Arithmetic.SmallLift]

theorem lift_injective : Function.Injective lift := by
  intro i j hij
  apply Fin.ext
  unfold lift at hij
  omega

























theorem tupleKey_eq {h J : ℕ} (t : ChoiceTuple h J) :
    tupleKey t = tupleRight t - tupleLeft t := by
  rw [tupleKey, globalKey, tupleRight, tupleLeft, positionalHash_difference]
  congr 1
  exact List.map_ofFn.symm






















































theorem tuple_mem_representations {h J : ℕ} (t : ChoiceTuple h J) (b c : ℤ) :
    List.ofFn t ∈ representations h J b c ↔
      globalModulus h J ∣ b - tupleLeft t ∧ globalModulus h J ∣ c - tupleRight t := by
  rw [mem_representations]
  simp only [List.length_ofFn, true_and, tupleLeft, tupleRight]

theorem tuple_difference_congruence {h J : ℕ} {t : ChoiceTuple h J} {b c : ℤ}
    (ht : List.ofFn t ∈ representations h J b c) :
    globalModulus h J ∣ (c - b) - tupleKey t := by
  obtain ⟨hb, hc⟩ := (tuple_mem_representations t b c).mp ht
  rw [tupleKey_eq]
  rw [sub_sub_sub_comm]
  exact dvd_sub hc hb












theorem mem_witnesses {h J : ℕ} {P d a b c : ℤ} {w : Witness h J} :
    w ∈ witnesses h J P d a b c ↔
      List.ofFn w.1 ∈ representations h J (b % P) (c % P + d) ∧
        globalModulus h J ∣ (a % P + lift w.2 * P + d) - tupleKey w.1 := by
  simp only [witnesses, Finset.mem_filter, Finset.mem_univ, true_and]

theorem witness_sound {h J : ℕ} {P d a b c : ℤ} {w : Witness h J}
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J)
    (hw : w ∈ witnesses h J P d a b c) : P ∣ c - b - a := by
  obtain ⟨hrep, hquery⟩ := mem_witnesses.mp hw
  have hdiff := tuple_difference_congruence hrep
  have hkey : Int.ModEq (globalModulus h J)
      (a % P + lift w.2 * P + d) (c % P + d - b % P) := by
    apply Int.modEq_of_dvd
    simpa only [sub_sub_sub_cancel_right] using dvd_sub hdiff hquery
  exact Arithmetic.guarded_remainder_lift_sound hP hguard (lift_small w.2) hkey
































/-- Projection to the retained list is injective on the raw witnesses of
one original triple: the guard makes its lift unique. -/
theorem witness_projection_injective {h J : ℕ} {P d a b c : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J) :
    Set.InjOn (fun w : Witness h J => List.ofFn w.1) (witnesses h J P d a b c) := by
  intro w hw v hv he
  have ht : w.1 = v.1 := List.ofFn_injective he
  have hwq := (mem_witnesses.mp hw).2
  have hvq := (mem_witnesses.mp hv).2
  have hd : globalModulus h J ∣
      (a % P + lift w.2 * P + d) - (a % P + lift v.2 * P + d) := by
    rw [ht] at hwq
    simpa only [sub_sub_sub_cancel_right] using dvd_sub hwq hvq
  have hj := Arithmetic.guarded_lift_unique hP hguard (lift_small w.2) (lift_small v.2) hd
  exact Prod.ext ht (lift_injective hj)

theorem witnesses_card_bound {h J : ℕ} {P d a b c : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J) :
    (witnesses h J P d a b c).card ≤ representationCap h J := by
  calc
    _ ≤ (representations h J (b % P) (c % P + d)).card := by
      apply Finset.card_le_card_of_injOn (fun w : Witness h J => List.ofFn w.1)
      · intro w hw
        exact (mem_witnesses.mp hw).1
      · exact witness_projection_injective hP hguard
    _ ≤ _ := representations_card_bound h J (b % P) (c % P + d)






























section OriginalIndices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]














theorem mem_rawOn {h J : ℕ} {P d : ℤ} {T : Finset (Original α β γ)}
    {a : α → ℤ} {b : β → ℤ} {c : γ → ℤ} {r : RawItem h J α β γ} :
    r ∈ rawOn h J P d T a b c ↔
      r.1 ∈ T ∧ r.2 ∈ witnesses h J P d (a r.1.1) (b r.1.2.1) (c r.1.2.2) :=
  Finset.mem_sigma

theorem raw_sound {h J : ℕ} {P d : ℤ} {T : Finset (Original α β γ)}
    {a : α → ℤ} {b : β → ℤ} {c : γ → ℤ} {r : RawItem h J α β γ}
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J)
    (hr : r ∈ rawOn h J P d T a b c) : P ∣ difference a b c r.1 :=
  witness_sound hP hguard (mem_rawOn.mp hr).2














theorem raw_owner_fiber_bound {h J : ℕ} {P d : ℤ} (T : Finset (Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ)
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J) (t : Original α β γ) :
    ((rawOn h J P d T a b c).filter fun r => r.1 = t).card ≤ representationCap h J := by
  calc
    _ ≤ (witnesses h J P d (a t.1) (b t.2.1) (c t.2.2)).card := by
      apply Finset.card_le_card_of_injOn (fun r : RawItem h J α β γ => r.2)
      · intro r hr
        obtain ⟨hr, ht⟩ := Finset.mem_filter.mp hr
        have hw := (mem_rawOn.mp hr).2
        simpa only [Finset.mem_coe, ht] using hw
      · intro r hr s hs he
        have hrt := (Finset.mem_filter.mp hr).2
        have hst := (Finset.mem_filter.mp hs).2
        exact Sigma.ext (hrt.trans hst.symm) (heq_of_eq he)
    _ ≤ _ := witnesses_card_bound hP hguard

theorem raw_owner_weight_bound {h J : ℕ} {P d : ℤ} (T : Finset (Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ)
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J) (t : Original α β γ) :
    Arithmetic.fiberWeight (rawOn h J P d T a b c) Sigma.fst (fun _ => 1) t ≤
      representationCap h J := by
  have he : Arithmetic.fiberWeight (rawOn h J P d T a b c) Sigma.fst (fun _ => 1) t =
      ((rawOn h J P d T a b c).filter fun r => r.1 = t).card := by
    simp only [Arithmetic.fiberWeight, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [he]
  exact raw_owner_fiber_bound T a b c hP hguard t


















































































/-- The dense stopping rule uses the actual guarded incidences and the
actual radix multiplicity bound. Its score is the weighted false-count
quantity computed by the arithmetic histogram identities. -/
theorem dense_early_yes_sourceProof {h J : ℕ} {P d : ℤ} (T : Finset (Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (aux : Finset ℤ)
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J)
    (hsep : ∀ t ∈ T, difference a b c t ≠ 0 → ∃ l ∈ aux, ¬l ∣ difference a b c t)
    (hlarge : representationCap h J * Arithmetic.weightedFalseCount T (difference a b c) aux P <
      rawMass h J P d T a b c) :
    ∃ t ∈ T, difference a b c t = 0 := by
  let good : Original α β γ → Prop :=
    fun t => t ∉ T ∨ ¬P ∣ difference a b c t ∨ difference a b c t = 0
  have hset : (Finset.univ.filter fun t : Original α β γ => ¬good t) =
      T.filter (fun t => P ∣ difference a b c t ∧ difference a b c t ≠ 0) := by
    ext t
    simp [good]
  have hcount : (Finset.univ.filter fun t : Original α β γ => ¬good t).card ≤
      Arithmetic.weightedFalseCount T (difference a b c) aux P := by
    rw [hset, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Arithmetic.falseCount_le_weightedFalseCount T (difference a b c) aux P hsep
  have hmass : representationCap h J * Arithmetic.weightedFalseCount T (difference a b c) aux P <
      ∑ _r ∈ rawOn h J P d T a b c, (1 : ℕ) := by
    simpa only [Finset.sum_const, smul_eq_mul, mul_one, rawMass] using hlarge
  obtain ⟨r, hr, _, hg⟩ := Arithmetic.early_yes
    (rawOn h J P d T a b c) Sigma.fst (fun _ => 1) good
    (representationCap h J) (Arithmetic.weightedFalseCount T (difference a b c) aux P)
    (fun t _ => raw_owner_weight_bound T a b c hP hguard t) hcount hmass
  have ht := (mem_rawOn.mp hr).1
  have hd := raw_sound hP hguard hr
  refine ⟨r.1, ht, ?_⟩
  rcases hg with hnot | hnot | hz
  · exact False.elim (hnot ht)
  · exact False.elim (hnot hd)
  · exact hz





































end OriginalIndices

end ThreeSum.RawIncidences

end

universe u_1 u_2 u_3

theorem solution : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [Fintype.{u_1} α] [Fintype.{u_2} β] [Fintype.{u_3} γ]
  [DecidableEq.{u_1 + 1} α] [DecidableEq.{u_2 + 1} β] [DecidableEq.{u_3 + 1} γ] {h J : Nat} {P d : Int}
  (T : Finset.{max (max u_3 u_2) u_1} (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ)) (a : α → Int)
  (b : β → Int) (c : γ → Int) (aux : Finset.{0} Int),
  @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) P →
    @LE.le.{0} Int Int.instLEInt
        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
          (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))) P)
        (ThreeSum.GlobalEncoding.globalModulus h J) →
      (∀ (t : ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ),
          @Membership.mem.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3}
              (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ)
              (Finset.{max (max u_3 u_2) u_1} (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ))
              (@SetLike.instMembership.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3}
                (Finset.{max (max u_3 u_2) u_1} (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ))
                (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ)
                (@Finset.instSetLike.{max (max u_1 u_2) u_3} (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ)))
              T t →
            @Ne.{1} Int (@ThreeSum.RawIncidences.difference.{u_1, u_2, u_3} α β γ a b c t)
                (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
              ∃ (l : Int),
                And
                  (@Membership.mem.{0, 0} Int (Finset.{0} Int)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Int) Int (@Finset.instSetLike.{0} Int)) aux l)
                  (Not
                    (@Dvd.dvd.{0} Int Int.instDvd l
                      (@ThreeSum.RawIncidences.difference.{u_1, u_2, u_3} α β γ a b c t)))) →
        @LT.lt.{0} Nat instLTNat
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (ThreeSum.GlobalEncoding.representationCap h J)
              (@ThreeSum.Arithmetic.weightedFalseCount.{max (max u_1 u_2) u_3}
                (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ) T
                (@ThreeSum.RawIncidences.difference.{u_1, u_2, u_3} α β γ a b c) aux P))
            (@ThreeSum.RawIncidences.rawMass.{u_1, u_2, u_3} α β γ h J P d T a b c) →
          ∃ (t : ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ),
            And
              (@Membership.mem.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3}
                (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ)
                (Finset.{max (max u_3 u_2) u_1} (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ))
                (@SetLike.instMembership.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3}
                  (Finset.{max (max u_3 u_2) u_1} (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ))
                  (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ)
                  (@Finset.instSetLike.{max (max u_1 u_2) u_3} (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ)))
                T t)
              (@Eq.{1} Int (@ThreeSum.RawIncidences.difference.{u_1, u_2, u_3} α β γ a b c t)
                (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) := by
  exact @ThreeSum.RawIncidences.dense_early_yes_sourceProof

#print axioms solution

-- Prove2me | solution 1 for ThreeSum.Arithmetic.small_lift_exists
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:36:19.716741+00:00
-- url     : https://prove2.me/submissions/c4558100-5a5b-4738-90cd-b7a9a50e8358

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

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






























































































/-- Completeness of the signed-lift list for any modular candidate.
In fact, canonical residues only need the lifts -1 and 0. -/
theorem small_lift_exists_sourceProof {P a b c : ℤ} (hP : 0 < P)
    (ha0 : 0 ≤ a) (haP : a < P)
    (hb0 : 0 ≤ b) (hbP : b < P)
    (hc0 : 0 ≤ c) (hcP : c < P)
    (hdiv : P ∣ c - b - a) :
    ∃ j : ℤ, SmallLift j ∧ c - b = a + j * P := by
  obtain ⟨j, hj⟩ := hdiv
  have hjlo : -1 ≤ j := by
    by_contra h
    have hj' : j ≤ -2 := by omega
    have hm := mul_le_mul_of_nonneg_left hj' hP.le
    nlinarith
  have hjhi : j ≤ 0 := by
    by_contra h
    have hj' : 1 ≤ j := by omega
    have hm := mul_le_mul_of_nonneg_left hj' hP.le
    nlinarith
  refine ⟨j, ?_, ?_⟩
  · unfold SmallLift
    omega
  · nlinarith

/-! ## The weighted false-count identity -/















































































































































/-! ## Exact early YES from per-original-triple representation caps -/



































































end ThreeSum.Arithmetic

end


theorem solution : ∀ {P a b c : Int},
  @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) P →
    @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) a →
      @LT.lt.{0} Int Int.instLTInt a P →
        @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) b →
          @LT.lt.{0} Int Int.instLTInt b P →
            @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) c →
              @LT.lt.{0} Int Int.instLTInt c P →
                @Dvd.dvd.{0} Int Int.instDvd P
                    (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
                      (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) c b) a) →
                  ∃ (j : Int),
                    And (ThreeSum.Arithmetic.SmallLift j)
                      (@Eq.{1} Int (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) c b)
                        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) a
                          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) j P))) := by
  exact @ThreeSum.Arithmetic.small_lift_exists_sourceProof

#print axioms solution

-- Prove2me | solution 1 for ThreeSum.KaratsubaInterface.capacity_lt_twice
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:43:53.875084+00:00
-- url     : https://prove2.me/submissions/771822cd-f0bc-411f-9cb8-e336631864bd

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba

section


/-!
# Arbitrary-length interface for the verified multiplication routine

These exact inequalities convert a requested positive coefficient length
to its power-of-two capacity. Polynomial padding preserves the represented
product. The fifth-power bounds include any fixed linear preparation and
folding overhead, so no real-exponent oracle is needed for the time bound.
-/

namespace ThreeSum.KaratsubaInterface

open ThreeSum.Karatsuba ThreeSum.LightKaratsuba Polynomial





theorem capacity_lt_twice_sourceProof {p : ℕ} (hp : 0 < p) : capacity p < 2 * p := by
  by_cases h1 : p = 1
  · subst p
    norm_num [capacity]
  have hp1 : 1 < p := by omega
  have hk : 0 < Nat.clog 2 p := Nat.clog_pos (by decide) hp1
  have hpred := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hp1
  rw [Nat.pred_eq_sub_one] at hpred
  calc
    capacity p = 2 * 2 ^ (Nat.clog 2 p - 1) := by
      unfold capacity
      conv_lhs =>
        rw [show Nat.clog 2 p = (Nat.clog 2 p - 1) + 1 by omega, pow_succ]
      rw [Nat.mul_comm]
    _ < 2 * p := Nat.mul_lt_mul_of_pos_left hpred (by decide)







































































end ThreeSum.KaratsubaInterface

end


theorem solution : ∀ {p : Nat},
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p →
    @LT.lt.{0} Nat instLTNat (ThreeSum.KaratsubaInterface.capacity p)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) p) := by
  exact @ThreeSum.KaratsubaInterface.capacity_lt_twice_sourceProof

#print axioms solution

-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightSwitchScalar.scalar_safe
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:03:48.585192+00:00
-- url     : https://prove2.me/submissions/717d9e7e-cebb-438d-97a1-194ff5a9d960

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Log
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightSwitchScalar
end ThreeSum.LightSwitchScalar
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightSwitchScalar
end ThreeSum1960614.Machine.ThreeSum.LightSwitchScalar

namespace ThreeSum1960614.Machine

/-! # Structural safety for the fixed scalar expressions of the cubic switch -/

namespace ThreeSum.LightSwitchScalar
open _root_.ThreeSum.LightSwitchScalar


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1600000



theorem pow_cost_left (B a b : ℕ) (hB : 1 ≤ B) : B^a ≤ B^(a+b+1) :=
  Nat.pow_le_pow_right hB (by omega)

theorem pow_cost_right (B a b : ℕ) (hB : 1 ≤ B) : B^b ≤ B^(a+b+1) :=
  Nat.pow_le_pow_right hB (by omega)

theorem sum_pow_le {B : ℕ} (hB : 2 ≤ B) (a b : ℕ) :
    B^a+B^b ≤ B^(a+b+1) := by
  have ha : B^a ≤ B^(a+b) := Nat.pow_le_pow_right (by omega) (by omega)
  have hb : B^b ≤ B^(a+b) := Nat.pow_le_pow_right (by omega) (by omega)
  calc
    _ ≤ B^(a+b)+B^(a+b) := Nat.add_le_add ha hb
    _ = B^(a+b)*2 := by ring
    _ ≤ B^(a+b)*B := Nat.mul_le_mul_left _ hB
    _ = _ := by rw [pow_succ]

theorem scalar_bound {B : ℕ} (hB : 2 ≤ B) (σ : _root_.ThreeSum1960614.Machine.Light.State)
    (hvars : ∀ i, |σ.loc i| ≤ (B : ℤ)) (e : _root_.ThreeSum1960614.Machine.Light.Expr) (he : _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchScalar.Small B e) :
    |e.val σ| ≤ ((B^e.cost : ℕ) : ℤ) := by
  induction e with
  | const n => simpa [_root_.ThreeSum1960614.Machine.Light.Expr.val,_root_.ThreeSum1960614.Machine.Light.Expr.cost,Int.abs_natCast] using (Int.ofNat_le.mpr he)
  | var i => simpa [_root_.ThreeSum1960614.Machine.Light.Expr.val,_root_.ThreeSum1960614.Machine.Light.Expr.cost] using hvars i
  | load e ih => exact False.elim he
  | op o a b ia ib =>
    have ha := ia he.1
    have hb := ib he.2
    have hadd : ((B^a.cost : ℕ) : ℤ)+(B^b.cost : ℕ) ≤
        ((B^(a.cost+b.cost+1) : ℕ) : ℤ) := by exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchScalar.sum_pow_le hB a.cost b.cost
    have hprod : ((B^a.cost : ℕ) : ℤ)*(B^b.cost : ℕ) ≤
        ((B^(a.cost+b.cost+1) : ℕ) : ℤ) := by
      have hh : B^a.cost*B^b.cost ≤ B^(a.cost+b.cost+1) := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by omega) (by omega)
      exact_mod_cast hh
    cases o with
    | add => exact (abs_add_le _ _).trans ((add_le_add ha hb).trans hadd)
    | sub =>
      change |a.val σ-b.val σ| ≤ _
      rw [sub_eq_add_neg]
      exact (abs_add_le _ _).trans ((add_le_add ha (by simpa only [abs_neg] using hb)).trans hadd)
    | mul =>
      change |a.val σ*b.val σ| ≤ _
      rw [abs_mul]
      exact (mul_le_mul ha hb (abs_nonneg _) (by positivity)).trans hprod



end ThreeSum.LightSwitchScalar

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchScalar

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 1600000
section

theorem ThreeSum1960614.Machine.ThreeSum.LightSwitchScalar.scalar_safe__implementation_e6edfa1cab {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {B : ℕ} (hB : 2 ≤ B) (σ : _root_.ThreeSum1960614.Machine.Light.State)
    (hvars : ∀ i, |σ.loc i| ≤ (B : ℤ)) (e : _root_.ThreeSum1960614.Machine.Light.Expr) (he : _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchScalar.Small B e)
    (hword : ((B^e.cost : ℕ) : ℤ) ≤ lim.word) : e.Safe lim σ := by
  induction e with
  | const n =>
    have hn : (n : ℤ) ≤ (B : ℤ) := Int.ofNat_le.mpr he
    simpa [_root_.ThreeSum1960614.Machine.Light.Expr.Safe,_root_.ThreeSum1960614.Machine.Light.Expr.cost] using hn.trans (by simpa [_root_.ThreeSum1960614.Machine.Light.Expr.cost] using hword)
  | var i => trivial
  | load e ih => exact False.elim he
  | op o a b ia ib =>
    have hwA : ((B^a.cost : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (_root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchScalar.pow_cost_left B a.cost b.cost (by omega))).trans hword
    have hwB : ((B^b.cost : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (_root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchScalar.pow_cost_right B a.cost b.cost (by omega))).trans hword
    exact ⟨ia he.1 hwA,ib he.2 hwB,(_root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchScalar.scalar_bound hB σ hvars (_root_.ThreeSum1960614.Machine.Light.Expr.op o a b) he).trans hword⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightSwitchScalar.scalar_safe__implementation_e6edfa1cab) := (@ThreeSum1960614.Machine.ThreeSum.LightSwitchScalar.scalar_safe__implementation_e6edfa1cab)

#print axioms solution

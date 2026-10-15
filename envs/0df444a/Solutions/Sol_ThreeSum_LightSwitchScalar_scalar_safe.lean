-- Prove2me | solution 1 for ThreeSum.LightSwitchScalar.scalar_safe
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:58:31.363422+00:00
-- url     : https://prove2.me/submissions/d2b784c7-77c4-46c2-b347-68c2b4b7132b

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Log
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light

section


/-! # Structural safety for the fixed scalar expressions of the cubic switch -/

namespace ThreeSum.LightSwitchScalar

open Light

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

theorem scalar_bound {B : ℕ} (hB : 2 ≤ B) (σ : State)
    (hvars : ∀ i, |σ.loc i| ≤ (B : ℤ)) (e : Expr) (he : Small B e) :
    |e.val σ| ≤ ((B^e.cost : ℕ) : ℤ) := by
  induction e with
  | const n => simpa [Expr.val,Expr.cost,Int.abs_natCast] using (Int.ofNat_le.mpr he)
  | var i => simpa [Expr.val,Expr.cost] using hvars i
  | load e ih => exact False.elim he
  | op o a b ia ib =>
    have ha := ia he.1
    have hb := ib he.2
    have hadd : ((B^a.cost : ℕ) : ℤ)+(B^b.cost : ℕ) ≤
        ((B^(a.cost+b.cost+1) : ℕ) : ℤ) := by exact_mod_cast sum_pow_le hB a.cost b.cost
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

theorem scalar_safe_sourceProof {lim : Limits} {B : ℕ} (hB : 2 ≤ B) (σ : State)
    (hvars : ∀ i, |σ.loc i| ≤ (B : ℤ)) (e : Expr) (he : Small B e)
    (hword : ((B^e.cost : ℕ) : ℤ) ≤ lim.word) : e.Safe lim σ := by
  induction e with
  | const n =>
    have hn : (n : ℤ) ≤ (B : ℤ) := Int.ofNat_le.mpr he
    simpa [Expr.Safe,Expr.cost] using hn.trans (by simpa [Expr.cost] using hword)
  | var i => trivial
  | load e ih => exact False.elim he
  | op o a b ia ib =>
    have hwA : ((B^a.cost : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (pow_cost_left B a.cost b.cost (by omega))).trans hword
    have hwB : ((B^b.cost : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (pow_cost_right B a.cost b.cost (by omega))).trans hword
    exact ⟨ia he.1 hwA,ib he.2 hwB,(scalar_bound hB σ hvars (.op o a b) he).trans hword⟩

end ThreeSum.LightSwitchScalar

end


theorem solution : ∀ {lim : Light.Limits} {B : Nat},
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) B →
    ∀ (σ : Light.State),
      (∀ (i : Nat),
          @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (σ.loc i))
            (@Nat.cast.{0} Int instNatCastInt B)) →
        ∀ (e : Light.Expr),
          ThreeSum.LightSwitchScalar.Small B e →
            @LE.le.{0} Int Int.instLEInt
                (@Nat.cast.{0} Int instNatCastInt
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) B e.cost))
                lim.word →
              Light.Expr.Safe lim σ e := by
  exact @ThreeSum.LightSwitchScalar.scalar_safe_sourceProof

#print axioms solution

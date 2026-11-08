-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGenerators.shellIndex401_eq_of_lpsMatrix401_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:51:42.259194+00:00
-- url     : https://prove2.me/submissions/c27f4eb1-2bd0-4786-8a20-6044aa0e8a2f

import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators
section
open scoped BigOperators
open scoped MatrixGroups
namespace QEC.Coding.BalancedProduct.LPSGenerators
open Matrix
open LPSArithmetic
private theorem fin_eq_of_natCast_eq_of_card_le
    {n q : ℕ} [NeZero q]
    (hnq : n ≤ q) {i j : Fin n}
    (h : (i.val : ZMod q) = (j.val : ZMod q)) : i = j := by
  rw [ZMod.natCast_eq_natCast_iff] at h
  change i.val % q = j.val % q at h
  rw [Nat.mod_eq_of_lt (i.isLt.trans_le hnq),
    Nat.mod_eq_of_lt (j.isLt.trans_le hnq)] at h
  exact Fin.ext h
end QEC.Coding.BalancedProduct.LPSGenerators
end

set_option autoImplicit false
open scoped BigOperators
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSGenerators
open Matrix
open LPSArithmetic
namespace QEC.Coding.BalancedProduct.LPSGenerators
theorem _root_.solution
    (q : ℕ) [Fact q.Prime] (hq : 40 < q)
    {t u : ShellIndex401}
    (hM : lpsMatrix401 q t = lpsMatrix401 q u) : t = u := by
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro hz
    change ((2 : ℕ) : ZMod q) = 0 at hz
    rw [ZMod.natCast_eq_zero_iff] at hz
    have : q ≤ 2 := Nat.le_of_dvd (by omega) hz
    omega
  have h00 := congrFun (congrFun hM (0 : Fin 2)) (0 : Fin 2)
  have h01 := congrFun (congrFun hM (0 : Fin 2)) (1 : Fin 2)
  have h10 := congrFun (congrFun hM (1 : Fin 2)) (0 : Fin 2)
  have h11 := congrFun (congrFun hM (1 : Fin 2)) (1 : Fin 2)
  simp [lpsMatrix401] at h00 h01 h10 h11
  have ha : (t.a : ZMod q) = (u.a : ZMod q) := by
    have hzero : (2 : ZMod q) * ((t.a : ZMod q) - (u.a : ZMod q)) = 0 := by
      linear_combination h00 + h11
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left h2)
  have hc : (t.c : ZMod q) = (u.c : ZMod q) := by
    have hzero : (2 : ZMod q) * ((t.c : ZMod q) - (u.c : ZMod q)) = 0 := by
      linear_combination h01 - h10
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left h2)
  have huEq :
      ((t.b : ZMod q) - (u.b : ZMod q)) * lpsX q +
          ((t.d : ZMod q) - (u.d : ZMod q)) * lpsY q = 0 := by
    have hzero : (2 : ZMod q) *
        (((t.b : ZMod q) - (u.b : ZMod q)) * lpsX q +
          ((t.d : ZMod q) - (u.d : ZMod q)) * lpsY q) = 0 := by
      linear_combination h00 - h11
    exact (mul_eq_zero.mp hzero).resolve_left h2
  have hvEq :
      -((t.b : ZMod q) - (u.b : ZMod q)) * lpsY q +
          ((t.d : ZMod q) - (u.d : ZMod q)) * lpsX q = 0 := by
    have hzero : (2 : ZMod q) *
        (-((t.b : ZMod q) - (u.b : ZMod q)) * lpsY q +
          ((t.d : ZMod q) - (u.d : ZMod q)) * lpsX q) = 0 := by
      linear_combination h01 + h10
    exact (mul_eq_zero.mp hzero).resolve_left h2
  have hroot := lpsX_sq_add_lpsY_sq_add_one q
  have hb : (t.b : ZMod q) = (u.b : ZMod q) := by
    apply sub_eq_zero.mp
    linear_combination
      -lpsX q * huEq + lpsY q * hvEq +
        ((t.b : ZMod q) - (u.b : ZMod q)) * hroot
  have hd : (t.d : ZMod q) = (u.d : ZMod q) := by
    apply sub_eq_zero.mp
    linear_combination
      -lpsY q * huEq - lpsX q * hvEq +
        ((t.d : ZMod q) - (u.d : ZMod q)) * hroot
  apply ShellIndex401.ext
  · apply fin_eq_of_natCast_eq_of_card_le (by omega : 10 ≤ q)
    dsimp [ShellIndex401.a] at ha
    push_cast at ha
    have hzero : (2 : ZMod q) *
        ((t.aIndex.val : ZMod q) - (u.aIndex.val : ZMod q)) = 0 := by
      linear_combination ha
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left h2)
  · apply fin_eq_of_natCast_eq_of_card_le (by omega : 41 ≤ q)
    dsimp [ShellIndex401.b] at hb
    push_cast at hb
    linear_combination hb
  · apply fin_eq_of_natCast_eq_of_card_le (by omega : 41 ≤ q)
    dsimp [ShellIndex401.c] at hc
    push_cast at hc
    linear_combination hc
  · apply fin_eq_of_natCast_eq_of_card_le (by omega : 41 ≤ q)
    dsimp [ShellIndex401.d] at hd
    push_cast at hd
    linear_combination hd
end QEC.Coding.BalancedProduct.LPSGenerators

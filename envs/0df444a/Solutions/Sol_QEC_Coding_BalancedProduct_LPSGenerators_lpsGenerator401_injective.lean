-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGenerators.lpsGenerator401_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:54:50.731094+00:00
-- url     : https://prove2.me/submissions/755de7bb-be67-4687-a250-32921b2a6473

import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_shellIndex401_eq_of_lpsMatrix401_eq
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_lpsGL401_det
section
open scoped BigOperators
open scoped MatrixGroups
namespace QEC.Coding.BalancedProduct.LPSGenerators
open Matrix
open LPSArithmetic
private theorem shell401_a_cast_ne_neg
    (q : ℕ) [Fact q.Prime] (hq : 40 < q)
    (t u : ShellIndex401) :
    (t.a : ZMod q) ≠ -(u.a : ZMod q) := by
  intro ha
  dsimp [ShellIndex401.a] at ha
  push_cast at ha
  have hsum' :
      (2 : ZMod q) * t.aIndex.val + 1 +
          ((2 : ZMod q) * u.aIndex.val + 1) = 0 := by
    linear_combination ha
  have hsum :
      ((2 * t.aIndex.val + 1 + (2 * u.aIndex.val + 1) : ℕ) : ZMod q) = 0 := by
    push_cast
    exact hsum'
  rw [ZMod.natCast_eq_zero_iff] at hsum
  exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) hsum
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
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Function.Injective
      (fun t : {t // t ∈ shell401} => lpsGenerator401 q hq t.1 t.2) := by
  intro t u hproj
  change Matrix.ProjGenLinGroup.mk (lpsGL401 q hq t.1 t.2) =
      Matrix.ProjGenLinGroup.mk (lpsGL401 q hq u.1 u.2) at hproj
  change QuotientGroup.mk' (Subgroup.center (GL (Fin 2) (ZMod q)))
      (lpsGL401 q hq t.1 t.2) =
    QuotientGroup.mk' (Subgroup.center (GL (Fin 2) (ZMod q)))
      (lpsGL401 q hq u.1 u.2) at hproj
  rw [QuotientGroup.mk'_eq_mk'] at hproj
  rcases hproj with ⟨z, hz, hmul⟩
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  rcases hz with ⟨lambda, rfl⟩
  have hdet := congrArg Matrix.GeneralLinearGroup.det hmul
  simp only [map_mul, Matrix.GeneralLinearGroup.det_scalar,
    Fintype.card_fin] at hdet
  have hdetEq :
      (lpsGL401 q hq t.1 t.2).det =
        (lpsGL401 q hq u.1 u.2).det := by
    apply Units.ext
    rw [lpsGL401_det q hq t.1 t.2, lpsGL401_det q hq u.1 u.2]
  have hlambdaSq : lambda ^ 2 = 1 := by
    apply mul_left_cancel
    calc
      (lpsGL401 q hq t.1 t.2).det * lambda ^ 2 =
          (lpsGL401 q hq u.1 u.2).det := hdet
      _ = (lpsGL401 q hq t.1 t.2).det := hdetEq.symm
      _ = (lpsGL401 q hq t.1 t.2).det * 1 := by simp
  have hlambdaValSq : (lambda : ZMod q) ^ 2 = 1 :=
    congrArg Units.val hlambdaSq
  rcases sq_eq_one_iff.mp hlambdaValSq with hlambdaVal | hlambdaVal
  · have hlambda : lambda = 1 := Units.ext hlambdaVal
    have hGL : lpsGL401 q hq t.1 t.2 = lpsGL401 q hq u.1 u.2 := by
      simpa [hlambda] using hmul
    apply Subtype.ext
    apply shellIndex401_eq_of_lpsMatrix401_eq q hq40
    exact congrArg Units.val hGL
  · exfalso
    have hlambda : lambda = -1 := Units.ext hlambdaVal
    have hval := congrArg Units.val hmul
    have h00 := congrFun (congrFun hval (0 : Fin 2)) (0 : Fin 2)
    have h11 := congrFun (congrFun hval (1 : Fin 2)) (1 : Fin 2)
    have h2 : (2 : ZMod q) ≠ 0 := by
      intro hz
      change ((2 : ℕ) : ZMod q) = 0 at hz
      rw [ZMod.natCast_eq_zero_iff] at hz
      have : q ≤ 2 := Nat.le_of_dvd (by omega) hz
      omega
    have ha : (t.1.a : ZMod q) = -(u.1.a : ZMod q) := by
      simp [hlambda, lpsGL401, lpsMatrix401,
        Matrix.GeneralLinearGroup.scalar] at h00 h11
      apply eq_neg_iff_add_eq_zero.mpr
      have hzero : (2 : ZMod q) *
          ((t.1.a : ZMod q) + (u.1.a : ZMod q)) = 0 := by
        linear_combination -h00 - h11
      exact (mul_eq_zero.mp hzero).resolve_left h2
    exact shell401_a_cast_ne_neg q hq40 t.1 u.1 ha
end QEC.Coding.BalancedProduct.LPSGenerators

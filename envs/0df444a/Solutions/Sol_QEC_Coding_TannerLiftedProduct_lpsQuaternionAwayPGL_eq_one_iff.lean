-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuaternionAwayPGL_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:27:56.426245+00:00
-- url     : https://prove2.me/submissions/4080838b-cd97-4fb1-afde-00f7daf6588d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionRing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionReduction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p)
    (t : lpsQuaternionAwaySubmonoid a.q) :
    lpsQuaternionAwayPGL a.q t = 1 ↔
      (a.q : ℤ) ∣ t.1.b ∧
        (a.q : ℤ) ∣ t.1.c ∧
          (a.q : ℤ) ∣ t.1.d := by
  rw [lpsQuaternionAwayPGL_apply,
    Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.center_eq_range_scalar]
  constructor
  · rintro ⟨lambda, hlambda⟩
    have hval := congrArg Units.val hlambda
    have h00 := congrFun (congrFun hval (0 : Fin 2)) (0 : Fin 2)
    have h01 := congrFun (congrFun hval (0 : Fin 2)) (1 : Fin 2)
    have h10 := congrFun (congrFun hval (1 : Fin 2)) (0 : Fin 2)
    have h11 := congrFun (congrFun hval (1 : Fin 2)) (1 : Fin 2)
    simp [Matrix.GeneralLinearGroup.scalar, lpsQuaternionAwayGL,
      lpsQuaternionMatrix] at h00 h01 h10 h11
    have h2 : (2 : ZMod a.q) ≠ 0 := by
      intro hz
      change ((2 : ℕ) : ZMod a.q) = 0 at hz
      rw [ZMod.natCast_eq_zero_iff] at hz
      have hqle : a.q ≤ 2 := Nat.le_of_dvd (by omega) hz
      have hp := a.degreePrime.pos
      have hlarge := a.large
      omega
    have hc : (t.1.c : ZMod a.q) = 0 := by
      have hzero : (2 : ZMod a.q) * (t.1.c : ZMod a.q) = 0 := by
        linear_combination h10 - h01
      exact (mul_eq_zero.mp hzero).resolve_left h2
    have hu : (t.1.b : ZMod a.q) * lpsResidueX a.q +
        (t.1.d : ZMod a.q) * lpsResidueY a.q = 0 := by
      have hzero : (2 : ZMod a.q) *
          ((t.1.b : ZMod a.q) * lpsResidueX a.q +
            (t.1.d : ZMod a.q) * lpsResidueY a.q) = 0 := by
        linear_combination -h00 + h11
      exact (mul_eq_zero.mp hzero).resolve_left h2
    have hv : -(t.1.b : ZMod a.q) * lpsResidueY a.q +
        (t.1.d : ZMod a.q) * lpsResidueX a.q = 0 := by
      have hzero : (2 : ZMod a.q) *
          (-(t.1.b : ZMod a.q) * lpsResidueY a.q +
            (t.1.d : ZMod a.q) * lpsResidueX a.q) = 0 := by
        linear_combination -h01 - h10
      exact (mul_eq_zero.mp hzero).resolve_left h2
    have hroot := lpsResidueX_sq_add_lpsResidueY_sq_add_one a.q
    have hb : (t.1.b : ZMod a.q) = 0 := by
      linear_combination
        -lpsResidueX a.q * hu + lpsResidueY a.q * hv +
          (t.1.b : ZMod a.q) * hroot
    have hd : (t.1.d : ZMod a.q) = 0 := by
      linear_combination
        -lpsResidueY a.q * hu - lpsResidueX a.q * hv +
          (t.1.d : ZMod a.q) * hroot
    exact ⟨
      (ZMod.intCast_zmod_eq_zero_iff_dvd t.1.b a.q).mp hb,
      (ZMod.intCast_zmod_eq_zero_iff_dvd t.1.c a.q).mp hc,
      (ZMod.intCast_zmod_eq_zero_iff_dvd t.1.d a.q).mp hd⟩
  · rintro ⟨hbDiv, hcDiv, hdDiv⟩
    have hb : (t.1.b : ZMod a.q) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd t.1.b a.q).mpr hbDiv
    have hc : (t.1.c : ZMod a.q) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd t.1.c a.q).mpr hcDiv
    have hd : (t.1.d : ZMod a.q) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd t.1.d a.q).mpr hdDiv
    have haSq : (t.1.a : ZMod a.q) ^ 2 = (t.1.norm : ZMod a.q) := by
      simp [LPSQuaternion.norm, hb, hc, hd]
    have ha : (t.1.a : ZMod a.q) ≠ 0 := by
      intro haZero
      have hnormZero : (t.1.norm : ZMod a.q) = 0 := by
        rw [← haSq, haZero]
        simp
      exact (isUnit_iff_ne_zero.mp t.2) hnormZero
    refine ⟨Units.mk0 (t.1.a : ZMod a.q) ha, ?_⟩
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change Matrix.scalar (Fin 2) (t.1.a : ZMod a.q) i j =
      lpsQuaternionMatrix a.q t.1 i j
    fin_cases i <;> fin_cases j <;>
      simp [lpsQuaternionMatrix, hb, hc, hd] <;>
      rfl
end QEC.Coding.TannerLiftedProduct

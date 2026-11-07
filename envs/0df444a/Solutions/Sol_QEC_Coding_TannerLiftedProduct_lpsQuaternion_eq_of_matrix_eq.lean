-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuaternion_eq_of_matrix_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:34:08.72281+00:00
-- url     : https://prove2.me/submissions/dea39d1a-127b-4a79-b671-02937cc701e0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Mathlib.Data.Finset.Interval
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionShell
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


section
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
private theorem int_eq_of_cast_eq_of_bounds
    {p q : ℕ} (hpq : 2 * p < q) {x y : ℤ}
    (hxlo : -(p : ℤ) ≤ x) (hxhi : x ≤ p)
    (hylo : -(p : ℤ) ≤ y) (hyhi : y ≤ p)
    (hcast : (x : ZMod q) = (y : ZMod q)) : x = y := by
  have hdiv : (q : ℤ) ∣ y - x :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub x y q).mp hcast
  have hpqz : (2 * p : ℤ) < q := by exact_mod_cast hpq
  have habs : |y - x| < (q : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have hzero : y - x = 0 := Int.eq_zero_of_abs_lt_dvd hdiv habs
  omega
end QEC.Coding.TannerLiftedProduct
end

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) {t u : LPSQuaternion}
    (ht : t ∈ lpsQuaternionShell p)
    (hu : u ∈ lpsQuaternionShell p)
    (hM : lpsQuaternionMatrix a.q t = lpsQuaternionMatrix a.q u) :
    t = u := by
  have h2 : (2 : ZMod a.q) ≠ 0 := by
    intro hz
    change ((2 : ℕ) : ZMod a.q) = 0 at hz
    rw [ZMod.natCast_eq_zero_iff] at hz
    have hqle : a.q ≤ 2 := Nat.le_of_dvd (by omega) hz
    have hp := a.degreePrime.pos
    have hlarge := a.large
    omega
  have h00 := congrFun (congrFun hM (0 : Fin 2)) (0 : Fin 2)
  have h01 := congrFun (congrFun hM (0 : Fin 2)) (1 : Fin 2)
  have h10 := congrFun (congrFun hM (1 : Fin 2)) (0 : Fin 2)
  have h11 := congrFun (congrFun hM (1 : Fin 2)) (1 : Fin 2)
  simp [lpsQuaternionMatrix] at h00 h01 h10 h11
  have ha : (t.a : ZMod a.q) = (u.a : ZMod a.q) := by
    have hzero : (2 : ZMod a.q) *
        ((t.a : ZMod a.q) - (u.a : ZMod a.q)) = 0 := by
      linear_combination h00 + h11
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left h2)
  have hc : (t.c : ZMod a.q) = (u.c : ZMod a.q) := by
    have hzero : (2 : ZMod a.q) *
        ((t.c : ZMod a.q) - (u.c : ZMod a.q)) = 0 := by
      linear_combination h01 - h10
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left h2)
  have huEq :
      ((t.b : ZMod a.q) - (u.b : ZMod a.q)) * lpsResidueX a.q +
          ((t.d : ZMod a.q) - (u.d : ZMod a.q)) * lpsResidueY a.q = 0 := by
    have hzero : (2 : ZMod a.q) *
        (((t.b : ZMod a.q) - (u.b : ZMod a.q)) * lpsResidueX a.q +
          ((t.d : ZMod a.q) - (u.d : ZMod a.q)) * lpsResidueY a.q) = 0 := by
      linear_combination h00 - h11
    exact (mul_eq_zero.mp hzero).resolve_left h2
  have hvEq :
      -((t.b : ZMod a.q) - (u.b : ZMod a.q)) * lpsResidueY a.q +
          ((t.d : ZMod a.q) - (u.d : ZMod a.q)) * lpsResidueX a.q = 0 := by
    have hzero : (2 : ZMod a.q) *
        (-((t.b : ZMod a.q) - (u.b : ZMod a.q)) * lpsResidueY a.q +
          ((t.d : ZMod a.q) - (u.d : ZMod a.q)) * lpsResidueX a.q) = 0 := by
      linear_combination h01 + h10
    exact (mul_eq_zero.mp hzero).resolve_left h2
  have hroot := lpsResidueX_sq_add_lpsResidueY_sq_add_one a.q
  have hb : (t.b : ZMod a.q) = (u.b : ZMod a.q) := by
    apply sub_eq_zero.mp
    linear_combination
      -lpsResidueX a.q * huEq + lpsResidueY a.q * hvEq +
        ((t.b : ZMod a.q) - (u.b : ZMod a.q)) * hroot
  have hd : (t.d : ZMod a.q) = (u.d : ZMod a.q) := by
    apply sub_eq_zero.mp
    linear_combination
      -lpsResidueY a.q * huEq - lpsResidueX a.q * hvEq +
        ((t.d : ZMod a.q) - (u.d : ZMod a.q)) * hroot
  have htBounds := (mem_lpsQuaternionBox_iff p t).mp
    ((Finset.mem_filter.mp ht).1)
  have huBounds := (mem_lpsQuaternionBox_iff p u).mp
    ((Finset.mem_filter.mp hu).1)
  have hpq : 2 * p < a.q := by
    have hp := a.degreePrime.pos
    have hlarge := a.large
    omega
  apply LPSQuaternion.ext
  · exact int_eq_of_cast_eq_of_bounds hpq
      htBounds.1 htBounds.2.1 huBounds.1 huBounds.2.1 ha
  · exact int_eq_of_cast_eq_of_bounds hpq
      htBounds.2.2.1 htBounds.2.2.2.1
      huBounds.2.2.1 huBounds.2.2.2.1 hb
  · exact int_eq_of_cast_eq_of_bounds hpq
      htBounds.2.2.2.2.1 htBounds.2.2.2.2.2.1
      huBounds.2.2.2.2.1 huBounds.2.2.2.2.2.1 hc
  · exact int_eq_of_cast_eq_of_bounds hpq
      htBounds.2.2.2.2.2.2.1 htBounds.2.2.2.2.2.2.2
      huBounds.2.2.2.2.2.2.1 huBounds.2.2.2.2.2.2.2 hd
end QEC.Coding.TannerLiftedProduct

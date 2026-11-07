-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuaternionPSL_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:35:04.031738+00:00
-- url     : https://prove2.me/submissions/2a061d75-2487-47a0-a5dd-707c77813638

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Mathlib.Data.Finset.Interval
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionShell
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternion_eq_of_matrix_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_toPGL_lpsQuaternionPSL
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


section
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
private theorem shell_a_cast_ne_neg
    (a : LPSResiduePrime p) (t u : LPSQuaternion)
    (ht : t ∈ lpsQuaternionShell p)
    (hu : u ∈ lpsQuaternionShell p) :
    (t.a : ZMod a.q) ≠ -(u.a : ZMod a.q) := by
  intro ha
  have hsum : ((t.a + u.a : ℤ) : ZMod a.q) = 0 := by
    push_cast
    linear_combination ha
  have hdiv : (a.q : ℤ) ∣ t.a + u.a :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (t.a + u.a) a.q).mp hsum
  have htNormalized := (mem_lpsQuaternionShell_iff
    a.degreePrime.pos t).mp ht
  have huNormalized := (mem_lpsQuaternionShell_iff
    a.degreePrime.pos u).mp hu
  have htBounds := (mem_lpsQuaternionBox_iff p t).mp
    ((Finset.mem_filter.mp ht).1)
  have huBounds := (mem_lpsQuaternionBox_iff p u).mp
    ((Finset.mem_filter.mp hu).1)
  have htPos : 0 < t.a := htNormalized.2.1
  have huPos : 0 < u.a := huNormalized.2.1
  have hnonneg : 0 ≤ t.a + u.a := by omega
  have hpq : (2 * p : ℤ) < a.q := by
    have hp := a.degreePrime.pos
    have hlarge := a.large
    exact_mod_cast (show 2 * p < a.q by omega)
  have hlt : t.a + u.a < (a.q : ℤ) :=
    calc
      t.a + u.a ≤ (p : ℤ) + p :=
        add_le_add htBounds.2.1 huBounds.2.1
      _ = (2 * p : ℤ) := by ring
      _ < (a.q : ℤ) := hpq
  have hzero := Int.eq_zero_of_dvd_of_nonneg_of_lt hnonneg hlt hdiv
  omega
end QEC.Coding.TannerLiftedProduct
end

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a : LPSResiduePrime p) :
    Function.Injective
      (fun t : {t // t ∈ lpsQuaternionShell p} =>
        lpsQuaternionPSL a t.1
          (norm_eq_of_mem_lpsQuaternionShell a.degreePrime.pos t.2)) := by
  intro t u hPSL
  let htNorm := norm_eq_of_mem_lpsQuaternionShell
    a.degreePrime.pos t.2
  let huNorm := norm_eq_of_mem_lpsQuaternionShell
    a.degreePrime.pos u.2
  have hproj : lpsQuaternionPGL a t.1 htNorm =
      lpsQuaternionPGL a u.1 huNorm := by
    rw [← toPGL_lpsQuaternionPSL a t.1 htNorm,
      ← toPGL_lpsQuaternionPSL a u.1 huNorm]
    exact congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL hPSL
  change Matrix.ProjGenLinGroup.mk (lpsQuaternionGL a t.1 htNorm) =
      Matrix.ProjGenLinGroup.mk (lpsQuaternionGL a u.1 huNorm) at hproj
  change QuotientGroup.mk' (Subgroup.center (GL (Fin 2) (ZMod a.q)))
      (lpsQuaternionGL a t.1 htNorm) =
    QuotientGroup.mk' (Subgroup.center (GL (Fin 2) (ZMod a.q)))
      (lpsQuaternionGL a u.1 huNorm) at hproj
  rw [QuotientGroup.mk'_eq_mk'] at hproj
  rcases hproj with ⟨z, hz, hmul⟩
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  rcases hz with ⟨lambda, rfl⟩
  have hdet := congrArg Matrix.GeneralLinearGroup.det hmul
  simp only [map_mul, Matrix.GeneralLinearGroup.det_scalar,
    Fintype.card_fin] at hdet
  have hdetEq :
      (lpsQuaternionGL a t.1 htNorm).det =
        (lpsQuaternionGL a u.1 huNorm).det := by
    apply Units.ext
    rw [lpsQuaternionGL_det a t.1 htNorm,
      lpsQuaternionGL_det a u.1 huNorm]
  have hlambdaSq : lambda ^ 2 = 1 := by
    apply mul_left_cancel
    calc
      (lpsQuaternionGL a t.1 htNorm).det * lambda ^ 2 =
          (lpsQuaternionGL a u.1 huNorm).det := hdet
      _ = (lpsQuaternionGL a t.1 htNorm).det := hdetEq.symm
      _ = (lpsQuaternionGL a t.1 htNorm).det * 1 := by simp
  have hlambdaValSq : (lambda : ZMod a.q) ^ 2 = 1 :=
    congrArg Units.val hlambdaSq
  rcases sq_eq_one_iff.mp hlambdaValSq with hlambdaVal | hlambdaVal
  · have hlambda : lambda = 1 := Units.ext hlambdaVal
    have hGL : lpsQuaternionGL a t.1 htNorm =
        lpsQuaternionGL a u.1 huNorm := by
      simpa [hlambda] using hmul
    apply Subtype.ext
    apply lpsQuaternion_eq_of_matrix_eq a t.2 u.2
    exact congrArg Units.val hGL
  · exfalso
    have hlambda : lambda = -1 := Units.ext hlambdaVal
    have hval := congrArg Units.val hmul
    have h00 := congrFun (congrFun hval (0 : Fin 2)) (0 : Fin 2)
    have h11 := congrFun (congrFun hval (1 : Fin 2)) (1 : Fin 2)
    have h2 : (2 : ZMod a.q) ≠ 0 := by
      intro hz
      change ((2 : ℕ) : ZMod a.q) = 0 at hz
      rw [ZMod.natCast_eq_zero_iff] at hz
      have hqle : a.q ≤ 2 := Nat.le_of_dvd (by omega) hz
      have hp := a.degreePrime.pos
      have hlarge := a.large
      omega
    have ha : (t.1.a : ZMod a.q) = -(u.1.a : ZMod a.q) := by
      simp [hlambda, lpsQuaternionGL, lpsQuaternionMatrix,
        Matrix.GeneralLinearGroup.scalar] at h00 h11
      apply eq_neg_iff_add_eq_zero.mpr
      have hzero : (2 : ZMod a.q) *
          ((t.1.a : ZMod a.q) + (u.1.a : ZMod a.q)) = 0 := by
        linear_combination -h00 - h11
      exact (mul_eq_zero.mp hzero).resolve_left h2
    exact shell_a_cast_ne_neg a t.1 u.1 t.2 u.2 ha
end QEC.Coding.TannerLiftedProduct

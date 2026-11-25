-- Prove2me | solution 1 for P2M_GroundTheory_Arith_Abelian_isCoprime____Sq_a9e3a7b07819
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:11.822341+00:00
-- url     : https://prove2.me/submissions/a59e8dac-3cb0-4870-aa0e-3441d9821839

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
import Theorems.Thm_GroundTheory_Arith_Abelian_Phi_eval
import Theorems.Thm_GroundTheory_Arith_Abelian_psiAt_eq_zero_iff
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
import Theorems.Thm_GroundTheory_Arith_Abelian_zsmul_eq_zero_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some



set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
variable {F : Type*} [Field F] (W : WeierstrassCurve F)
variable [W.IsElliptic]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (n : ℤ) : IsCoprime (W.Φ n) (W.ΨSq n) := by
  classical
  set K := AlgebraicClosure F
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed F K]
  intro a
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨h1, h2⟩ := hcon
  set W' := W.map (algebraMap F K)
  have e1 : (W'.Φ n).eval a = 0 := by rw [map_Φ, eval_map_algebraMap, h1]
  have e2 : (W'.ΨSq n).eval a = 0 := by rw [map_ΨSq, eval_map_algebraMap, h2]
  obtain ⟨y, hy⟩ : ∃ y, W'.toAffine.Equation a y := by
    set b := W'.a₁ * a + W'.a₃
    set c := a ^ 3 + W'.a₂ * a ^ 2 + W'.a₄ * a + W'.a₆
    have hdeg : (X ^ 2 + C b * X - C c : K[X]).degree = 2 := by compute_degree!
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (X ^ 2 + C b * X - C c : K[X])
      (by rw [hdeg]; exact two_ne_zero)
    refine ⟨y, ?_⟩
    rw [equation_iff]
    simp only [IsRoot, eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X, b, c] at hy
    linear_combination hy
  have h : W'.toAffine.Nonsingular a y := (equation_iff_nonsingular).mp hy
  have hn0 : n • Point.some a y h = 0 := (zsmul_eq_zero_iff W' h n).mpr e2
  have hw : psiAt W' a y n = 0 := (psiAt_eq_zero_iff W' h n).mpr e2
  have hphi := Phi_eval W' h.1 n
  rw [e1, hw] at hphi
  have hprod : psiAt W' a y (n + 1) * psiAt W' a y (n - 1) = 0 := by linear_combination hphi
  rcases mul_eq_zero.mp hprod with hp | hp
  · have := (zsmul_eq_zero_iff W' h (n + 1)).mpr ((psiAt_eq_zero_iff W' h _).mp hp)
    rw [add_zsmul, one_zsmul, hn0, zero_add] at this
    exact Point.some_ne_zero h this
  · have := (zsmul_eq_zero_iff W' h (n - 1)).mpr ((psiAt_eq_zero_iff W' h _).mp hp)
    rw [sub_zsmul, one_zsmul, hn0, zero_add, neg_eq_zero] at this
    exact Point.some_ne_zero h this
end GroundTheory.Arith.Abelian

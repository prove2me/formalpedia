-- Prove2me | solution 1 for WeierstrassCurve.Affine.Point.isIntegral_of_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/53b17b76-cb2d-5f0a-a849-9abbb6e464d6

import Mathlib
import Theorems.Thm_WeierstrassCurve_Affine_Point_eval_psiSq_eq_zero_of_smul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_Point_isIntegral_of_smul_eq_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open scoped NNReal WeierstrassCurve.Affine
open WeierstrassCurve Polynomial

set_option maxHeartbeats 4000000

theorem solution
    {F : Type*} [Field F] {L : Type*} [Field L] [Algebra F L] [DecidableEq L]
    {W : WeierstrassCurve F} [W.IsElliptic] {n : ℤ} (hn : (n : F) ≠ 0)
    {x y : L} (hns : (W⁄L).Nonsingular x y)
    (hQ : n • (WeierstrassCurve.Affine.Point.some x y hns : (W⁄L).Point) = 0) :
    _root_.IsIntegral F x ∧ _root_.IsIntegral F y := by

  haveI hEL : (W⁄L).IsElliptic := W.instIsEllipticMap (algebraMap F L)

  have hΨ0 : ((W⁄L).ΨSq n).eval x = 0 :=
    WeierstrassCurve.Affine.Point.eval_psiSq_eq_zero_of_smul_eq_zero hns hQ

  have hmap : (W⁄L).ΨSq n = (W.ΨSq n).map (algebraMap F L) := W.map_ΨSq (algebraMap F L) n
  rw [hmap, Polynomial.eval_map] at hΨ0

  have hne : W.ΨSq n ≠ 0 := W.ΨSq_ne_zero hn
  have hx_int : _root_.IsIntegral F x :=
    IsAlgebraic.isIntegral ⟨W.ΨSq n, hne, by rwa [Polynomial.aeval_def]⟩
  refine ⟨hx_int, ?_⟩

  set R : Subalgebra F L := integralClosure F L with hR

  haveI hIR : Algebra.IsIntegral F R := ⟨fun a => (isIntegral_algHom_iff R.val
    Subtype.val_injective).mp a.2⟩

  have hxR : x ∈ R := hx_int
  have haR : ∀ a : F, algebraMap F L a ∈ R := fun a => isIntegral_algebraMap

  have heq : y ^ 2 + (W⁄L).a₁ * x * y + (W⁄L).a₃ * y
      = x ^ 3 + (W⁄L).a₂ * x ^ 2 + (W⁄L).a₄ * x + (W⁄L).a₆ :=
    (WeierstrassCurve.Affine.equation_iff x y).mp hns.1

  have hy_intR : _root_.IsIntegral R y := by
    have hc₁ : (W⁄L).a₁ * x + (W⁄L).a₃ ∈ R := by
      rw [WeierstrassCurve.Affine.baseChange_a₁, WeierstrassCurve.Affine.baseChange_a₃]
      exact add_mem (mul_mem (haR _) hxR) (haR _)
    have hc₀ : x ^ 3 + (W⁄L).a₂ * x ^ 2 + (W⁄L).a₄ * x + (W⁄L).a₆ ∈ R := by
      rw [WeierstrassCurve.Affine.baseChange_a₂, WeierstrassCurve.Affine.baseChange_a₄,
        WeierstrassCurve.Affine.baseChange_a₆]
      exact add_mem (add_mem (add_mem (pow_mem hxR 3) (mul_mem (haR _) (pow_mem hxR 2)))
        (mul_mem (haR _) hxR)) (haR _)
    refine ⟨X ^ 2 + (C (⟨_, hc₁⟩ : R) * X - C (⟨_, hc₀⟩ : R)), ?_, ?_⟩
    ·
      apply (monic_X_pow 2).add_of_left
      rw [degree_X_pow]
      refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt (degree_C_mul_X_le _) (by norm_num)
      · exact lt_of_le_of_lt degree_C_le (by norm_num)
    ·
      have halg : ∀ (c : L) (hc : c ∈ R), algebraMap R L ⟨c, hc⟩ = c := fun c hc => rfl
      simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, halg]
      linear_combination heq
  exact isIntegral_trans y hy_intR

end S_WeierstrassCurve_Affine_Point_isIntegral_of_smul_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_Affine_Point_isIntegral_of_smul_eq_zero (solution)

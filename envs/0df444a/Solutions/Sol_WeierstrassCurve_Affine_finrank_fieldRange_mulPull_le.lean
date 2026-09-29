-- Prove2me | solution 1 for WeierstrassCurve.Affine.finrank_fieldRange_mulPull_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/649de834-7f94-51f9-bb61-ea7b1d25267f

import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Definitions.Def_EllipticCurve_FunctionFieldPullback
import Theorems.Thm_WeierstrassCurve_Affine_FunctionField_adjoin_X_Y_eq_top
import Theorems.Thm_IntermediateField_finrank_fieldRange_le_of_adjoin_pair_eq_top
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_natDegree_Phi_sub_C_mul_PsiSq
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_psi_sq
import Theorems.Thm_WeierstrassCurve_Psi2Sq_ne_zero_of_isElliptic
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
import Theorems.Thm_WeierstrassCurve_Affine_Point_two_smul_some_eq_zero_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_finrank_fieldRange_mulPull_le
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open Polynomial IntermediateField

theorem solution {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℤ} (hgood : MulGood W K n) : FiniteDimensional (mulPull W K n).fieldRange (W⁄K).FunctionField ∧ Module.finrank (mulPull W K n).fieldRange (W⁄K).FunctionField ≤ n.natAbs ^ 2 := by
  classical
  haveI hEK : (W⁄K).IsElliptic := by
    dsimp only [Affine.baseChange, WeierstrassCurve.baseChange]; infer_instance
  set L := (W⁄K).FunctionField with hL
  set gX := genericX W K with hXdef
  set gY := genericY W K with hYdef
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hgood.1 (zero_zsmul _)

  let f : K →ₐ[F] L := IsScalarTower.toAlgHom F K L
  have hf : (f : K →+* L) = algebraMap K L := rfl
  have hΦ : (W⁄L).Φ n = ((W⁄K).Φ n).map (algebraMap K L) := by
    rw [← hf]; exact W.baseChange_Φ f n
  have hΨSq : (W⁄L).ΨSq n = ((W⁄K).ΨSq n).map (algebraMap K L) := by
    rw [← hf]; exact W.baseChange_ΨSq f n
  have hΨ₂Sq : (W⁄L).Ψ₂Sq = (W⁄K).Ψ₂Sq.map (algebraMap K L) := by
    rw [← hf]; exact W.baseChange_Ψ₂Sq f

  have hγn : n • genericPoint W K ≠ 0 := hgood.1
  have hψ : ((W⁄L).ψ n).evalEval gX gY ≠ 0 := fun h0 =>
    hγn ((WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff (W⁄L) (generic_nonsingular W K) n).mpr h0)
  have hΨX : ((W⁄L).ΨSq n).eval gX ≠ 0 := by
    rw [← WeierstrassCurve.Affine.evalEval_psi_sq (W⁄L) (generic_equation W K) n]
    exact pow_ne_zero _ hψ

  obtain ⟨y', h', hmul⟩ :=
    WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div (W⁄L) (generic_nonsingular W K) hψ
  have hxn : mulPull W K n gX = ((W⁄L).Φ n).eval gX / ((W⁄L).ΨSq n).eval gX := by
    rw [hXdef, mulPull_genericX' W K hgood]
    show (n • Point.some _ _ (generic_nonsingular W K)).xc = _
    rw [hmul, Point.xc_some]

  set A : L := (W⁄L).a₁ * gX + (W⁄L).a₃ with hA
  set B : L := -(gX ^ 3 + (W⁄L).a₂ * gX ^ 2 + (W⁄L).a₄ * gX + (W⁄L).a₆) with hB
  have hcoef : ∀ a : F, (algebraMap F L a) ∈ K⟮gX⟯ := fun a => by
    rw [IsScalarTower.algebraMap_apply F K L]
    exact IntermediateField.algebraMap_mem _ _
  have ha₁ : (W⁄L).a₁ = algebraMap F L W.a₁ := rfl
  have ha₂ : (W⁄L).a₂ = algebraMap F L W.a₂ := rfl
  have ha₃ : (W⁄L).a₃ = algebraMap F L W.a₃ := rfl
  have ha₄ : (W⁄L).a₄ = algebraMap F L W.a₄ := rfl
  have ha₆ : (W⁄L).a₆ = algebraMap F L W.a₆ := rfl
  have hXKX : gX ∈ K⟮gX⟯ := mem_adjoin_simple_self K gX
  have hAmem : A ∈ K⟮gX⟯ := by
    rw [hA, ha₁, ha₃]
    exact add_mem (mul_mem (hcoef _) hXKX) (hcoef _)
  have hBmem : B ∈ K⟮gX⟯ := by
    rw [hB, ha₂, ha₄, ha₆]
    refine neg_mem (add_mem (add_mem (add_mem (pow_mem hXKX 3) (mul_mem (hcoef _) (pow_mem hXKX 2)))
      (mul_mem (hcoef _) hXKX)) (hcoef _))
  have hYq : gY ^ 2 + A * gY + B = 0 := by
    have h := (equation_iff _ _).mp (generic_equation W K)
    rw [hA, hB]
    linear_combination h

  have hιX : (negEquiv W K : L →ₐ[K] L) gX = gX := negEquiv_genericX W K
  have hιY' : (negEquiv W K : L →ₐ[K] L) gY = -gY - A := by
    show negEquiv W K (genericY W K) = _
    rw [negEquiv_genericY, WeierstrassCurve.Affine.negY, hA]
    ring
  have hιY : ((negEquiv W K : L →ₐ[K] L) gY) ^ 2 + A * (negEquiv W K : L →ₐ[K] L) gY + B = 0 := by
    rw [hιY']
    linear_combination hYq
  have hιμ : (negEquiv W K : L →ₐ[K] L) (mulPull W K n gY) ≠ mulPull W K n gY := by
    intro heq
    change negEquiv W K (mulPull W K n (genericY W K)) = mulPull W K n (genericY W K) at heq
    rw [negEquiv_mulPull_genericY' W K hgood, mulPull_genericY' W K hgood] at heq

    have hP := Point.eq_some_xc_yc hγn
    have h2 : (2 : ℕ) • (n • genericPoint W K) = 0 := by
      rw [two_nsmul, add_eq_zero_iff_eq_neg]
      conv_rhs => rw [hP, Point.neg_some]
      conv_lhs => rw [hP]
      congr 1
      exact heq.symm
    rw [hP, WeierstrassCurve.Affine.Point.two_smul_some_eq_zero_iff (W⁄L), hΨ₂Sq,
      eval_map_algebraMap] at h2

    apply not_isIntegral_xc_of_ne_baseChange (n • genericPoint W K) hgood.1 hgood.2
    exact IsAlgebraic.isIntegral ⟨(W⁄K).Ψ₂Sq, WeierstrassCurve.Psi2Sq_ne_zero_of_isElliptic (W⁄K), h2⟩

  have hgen : IntermediateField.adjoin K {gX, gY} = ⊤ := FunctionField.adjoin_X_Y_eq_top (W⁄K)
  have key := IntermediateField.finrank_fieldRange_le_of_adjoin_pair_eq_top gX gY hgen A B hAmem hBmem hYq (mulPull W K n)
    (negEquiv W K : L →ₐ[K] L) hιX hιY hιμ ((W⁄K).Φ n) ((W⁄K).ΨSq n)
    (d := n.natAbs ^ 2) (pow_pos (Int.natAbs_pos.mpr hn0) 2) ?_ ?_
  · exact key
  ·
    rw [← eval_map_algebraMap, ← eval_map_algebraMap, ← hΦ, ← hΨSq, hxn, div_mul_cancel₀ _ hΨX]
  · intro M c
    rw [← WeierstrassCurve.map_Φ, ← WeierstrassCurve.map_ΨSq]
    exact WeierstrassCurve.natDegree_Phi_sub_C_mul_PsiSq _ n c

end S_WeierstrassCurve_Affine_finrank_fieldRange_mulPull_le
end P2MW
export P2MW.S_WeierstrassCurve_Affine_finrank_fieldRange_mulPull_le (solution)

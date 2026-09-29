-- Prove2me | solution 1 for WeierstrassCurve.exists_trace_of_equivOfVariableChangeEq_symm_apply_eq_val_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/8e3c8bfd-6a59-541f-9b5a-e73f67c2b9be

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero
import Theorems.Thm_AddMonoidHom_sub_mul_add_one_smul_eq_zero_of_comp_self_sub_smul_add_eq_zero_of_apply_eq_smul
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_trace_of_equivOfVariableChangeEq_symm_apply_eq_val_smul
p2m_attr_erase "instance" "ModularCurve.Gamma0Pair.isElliptic instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two"

set_option autoImplicit false

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_trace_of_equivOfVariableChangeEq_symm_apply_eq_val_smul.WeierstrassCurve WeierstrassCurve.Affine"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine toAffine VariableChange exists_int_transport_comp_sub_smul_add_eq_zero"
namespace TraceClause
p2m_open "WeierstrassCurve"

theorem equivOfVariableChangeEq_symm_add {K : Type*} [Field K] [DecidableEq K]
    (C : VariableChange K) (W : WeierstrassCurve.Affine K) {V : WeierstrassCurve.Affine K} (h : C • W = V)
    (P Q : W.Point) :
    (Point.equivOfVariableChangeEq (W := W) h).symm (P + Q) =
      (Point.equivOfVariableChangeEq (W := W) h).symm P + (Point.equivOfVariableChangeEq (W := W) h).symm Q := by
  subst h
  exact Point.vcInvFun_add C W P Q

end WeierstrassCurve.TraceClause

open WeierstrassCurve.TraceClause in
theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (M : ℕ) [NeZero M] (E₀ : WeierstrassCurve K) [E₀.IsElliptic]
    (P₀ : E₀.toAffine.Point) (hP₀ : addOrderOf P₀ = M)
    (α : VariableChange K) (hα : α • E₀ = E₀) (lam : (ZMod M)ˣ)
    (h : (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm P₀ = ((lam : ZMod M).val) • P₀) :
    ∃ t : ℤ, (t = -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2) ∧
      ((lam : ZMod M) ^ 2 - (t : ZMod M) * (lam : ZMod M) + 1 = 0) ∧
      (t = 2 → lam = 1) ∧ (t = -2 → lam = -1) := by
  obtain ⟨t, ht, hCH, h2, hm2⟩ :=
    WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero K p E₀ α hα
  set σ := (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm with hσ

  let m : E₀.toAffine.Point →+ E₀.toAffine.Point :=
    AddMonoidHom.mk' σ (equivOfVariableChangeEq_symm_add α E₀.toAffine hα)
  have hm : ∀ T, m (m T) - t • m T + T = 0 := hCH

  set c : ℤ := ((lam : ZMod M).val : ℤ) with hc
  have hP : m P₀ = c • P₀ := by
    show σ P₀ = c • P₀
    rw [h, hc, natCast_zsmul]
  have key : (c ^ 2 - t * c + 1) • P₀ = 0 :=
    AddMonoidHom.sub_mul_add_one_smul_eq_zero_of_comp_self_sub_smul_add_eq_zero_of_apply_eq_smul m t hm P₀ c hP

  have hcast : ((c : ℤ) : ZMod M) = (lam : ZMod M) := by
    rw [hc, Int.cast_natCast, ZMod.natCast_zmod_val]
  have zmod_of_zsmul : ∀ n : ℤ, n • P₀ = 0 → ((n : ℤ) : ZMod M) = 0 := by
    intro n hn
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← hP₀]
    exact (addOrderOf_dvd_iff_zsmul_eq_zero).mpr hn
  refine ⟨t, ht, ?_, ?_, ?_⟩
  · have := zmod_of_zsmul _ key
    push_cast at this
    rw [hcast] at this
    linear_combination this
  · intro ht2
    have hfix : σ P₀ = P₀ := h2 ht2 P₀
    rw [h] at hfix
    have h0 : (c - 1) • P₀ = 0 := by rw [sub_zsmul, one_zsmul, hc, natCast_zsmul, hfix]; simp
    have := zmod_of_zsmul _ h0
    push_cast at this
    rw [hcast, sub_eq_zero] at this
    exact Units.ext this
  · intro htm2
    have hneg : σ P₀ = -P₀ := hm2 htm2 P₀
    rw [h] at hneg
    have h0 : (c + 1) • P₀ = 0 := by rw [add_zsmul, one_zsmul, hc, natCast_zsmul, hneg]; simp
    have := zmod_of_zsmul _ h0
    push_cast at this
    rw [hcast, ← eq_neg_iff_add_eq_zero] at this
    exact Units.ext (by simpa using this)

end S_WeierstrassCurve_exists_trace_of_equivOfVariableChangeEq_symm_apply_eq_val_smul
end P2MW
export P2MW.S_WeierstrassCurve_exists_trace_of_equivOfVariableChangeEq_symm_apply_eq_val_smul (solution)

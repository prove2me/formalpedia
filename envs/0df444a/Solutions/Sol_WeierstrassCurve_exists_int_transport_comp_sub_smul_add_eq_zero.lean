-- Prove2me | solution 1 for WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/17ddca48-c51d-54b0-9c63-40c7c7e19478

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero_of_natCard_stabilizer_eq_two
import Theorems.Thm_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_zero_of_two_ne_zero
import Theorems.Thm_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_1728_of_two_ne_zero
import Theorems.Thm_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_zero_of_charP_two
import Theorems.Thm_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_zero_of_charP_three
import Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728
import Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero
p2m_attr_erase "instance" "ModularCurve.Gamma0Pair.isElliptic instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two"

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (α : WeierstrassCurve.VariableChange K) (hα : α • E₀ = E₀) :
    ∃ t : ℤ, (t = -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2) ∧
      (∀ T : E₀.toAffine.Point,
        (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm
            ((Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T)
          - t • (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T + T = 0) ∧
      (t = 2 → ∀ T : E₀.toAffine.Point, (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T = T) ∧
      (t = -2 → ∀ T : E₀.toAffine.Point, (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T = -T) := by
  have hchar : ringChar K = p := ringChar.eq K p
  by_cases hp2 : p = 2
  · subst hp2
    by_cases hj : E₀.j = 0
    · exact WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_zero_of_charP_two K E₀ hj α hα
    · exact WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero_of_natCard_stabilizer_eq_two K E₀
        (WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three (Or.inl hchar) E₀ hj) α hα
  · by_cases hp3 : p = 3
    · subst hp3
      by_cases hj : E₀.j = 0
      · exact WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_zero_of_charP_three K E₀ hj α hα
      · exact WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero_of_natCard_stabilizer_eq_two K E₀
          (WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three (Or.inr hchar) E₀ hj) α hα
    ·
      have h2 : (2 : K) ≠ 0 := by
        intro h
        have : ringChar K ∣ 2 := (ringChar.spec K 2).mp (by exact_mod_cast h)
        rw [hchar] at this
        have := (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this
        exact hp2 this
      have h3 : (3 : K) ≠ 0 := by
        intro h
        have : ringChar K ∣ 3 := (ringChar.spec K 3).mp (by exact_mod_cast h)
        rw [hchar] at this
        have := (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_three).mp this
        exact hp3 this
      by_cases hj0 : E₀.j = 0
      · exact WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_zero_of_two_ne_zero K h2 h3 E₀ hj0 α hα
      · by_cases hj1728 : E₀.j = 1728
        · exact WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_1728_of_two_ne_zero K h2 h3 E₀ hj1728 α hα
        · exact WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero_of_natCard_stabilizer_eq_two K E₀
            (WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728 h2 h3 E₀ hj0 hj1728) α hα

end S_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero (solution)

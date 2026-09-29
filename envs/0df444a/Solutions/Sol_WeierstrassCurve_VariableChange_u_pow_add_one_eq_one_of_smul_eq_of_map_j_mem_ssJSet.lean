-- Prove2me | solution 1 for WeierstrassCurve.VariableChange.u_pow_add_one_eq_one_of_smul_eq_of_map_j_mem_ssJSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/a26d80d5-b57e-5c15-9bc6-835081cc6860

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728
import Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_dvd_four_of_j_eq_1728
import Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_dvd_six_of_j_eq_zero
import Theorems.Thm_ModularCurve_ssJSet_eq_ssJSetHasse
import Theorems.Thm_ModularCurve_ofNat1728_mem_ssJSetHasse_iff
import Theorems.Thm_ModularCurve_zero_mem_ssJSetHasse_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_VariableChange_u_pow_add_one_eq_one_of_smul_eq_of_map_j_mem_ssJSet
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

namespace AutScalarS1

open WeierstrassCurve

theorem u_pow {R : Type*} [CommRing R] (C : VariableChange R) (n : ℕ) :
    (C ^ n).u = C.u ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, VariableChange.one_def]
  | succ n ih => rw [pow_succ, pow_succ, VariableChange.mul_def, ← ih]

theorem val_u_pow_eq_one_of_smul_eq {F : Type*} [Field F] (E : WeierstrassCurve F)
    (C : VariableChange F) (hC : C • E = E) (n : ℕ)
    (hcard : Nat.card (MulAction.stabilizer (VariableChange F) E) ∣ n) :
    (C.u : F) ^ n = 1 := by
  have hmem : C ∈ MulAction.stabilizer (VariableChange F) E := MulAction.mem_stabilizer_iff.mpr hC
  have h1 : (⟨C, hmem⟩ : MulAction.stabilizer (VariableChange F) E) ^ n = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard _).trans hcard)
  have h2 : C ^ n = 1 := by
    have h := congrArg Subtype.val h1
    simpa using h
  have h3 : C.u ^ n = 1 := by
    rw [← u_pow, h2, VariableChange.one_def]
  have h4 := congrArg Units.val h3
  simpa using h4

theorem pow_eq_one_of_pow_eq_one_of_dvd {F : Type*} [Monoid F] (x : F) (n m : ℕ) (h : x ^ n = 1)
    (hd : n ∣ m) : x ^ m = 1 := by
  obtain ⟨k, rfl⟩ := hd
  rw [pow_mul, h, one_pow]

end AutScalarS1

open AutScalarS1 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (k : Type) [Field k] [CharP k q] (W : WeierstrassCurve k) [W.IsElliptic]
    (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω] (ι : k →+* Ω)
    (hss : ι W.j ∈ ModularCurve.ssJSet q Ω)
    (C : WeierstrassCurve.VariableChange k) (hC : C • W = W) :
    (C.u : k) ^ (q + 1) = 1 := by
  have hprime : q.Prime := Fact.out
  have hq2 : q ≠ 2 := by omega
  have hodd : q % 2 = 1 := Nat.odd_iff.mp (hprime.odd_of_ne_two hq2)
  have h2 : (2 : k) ≠ 0 := by
    rw [show (2 : k) = ((2 : ℕ) : k) by norm_num, ne_eq, CharP.cast_eq_zero_iff k q]
    intro h
    have := Nat.le_of_dvd two_pos h
    omega
  have h3 : (3 : k) ≠ 0 := by
    rw [show (3 : k) = ((3 : ℕ) : k) by norm_num, ne_eq, CharP.cast_eq_zero_iff k q]
    intro h
    have := Nat.le_of_dvd three_pos h
    omega
  rw [ModularCurve.ssJSet_eq_ssJSetHasse q hq2 Ω] at hss
  by_cases hj0 : W.j = 0
  ·
    have h6 : (C.u : k) ^ 6 = 1 :=
      val_u_pow_eq_one_of_smul_eq W C hC 6
        (WeierstrassCurve.natCard_stabilizer_variableChange_dvd_six_of_j_eq_zero h2 h3 W hj0)
    have hq3 : q % 3 = 2 := by
      rw [hj0, map_zero] at hss
      exact (ModularCurve.zero_mem_ssJSetHasse_iff q hq Ω).mp hss
    exact pow_eq_one_of_pow_eq_one_of_dvd _ 6 _ h6 (by omega)
  by_cases hj1728 : W.j = 1728
  ·
    have h4 : (C.u : k) ^ 4 = 1 :=
      val_u_pow_eq_one_of_smul_eq W C hC 4
        (WeierstrassCurve.natCard_stabilizer_variableChange_dvd_four_of_j_eq_1728 h2 h3 W hj1728)
    have hq4 : q % 4 = 3 := by
      rw [hj1728, map_ofNat] at hss
      exact (ModularCurve.ofNat1728_mem_ssJSetHasse_iff q hq Ω).mp hss
    exact pow_eq_one_of_pow_eq_one_of_dvd _ 4 _ h4 (by omega)
  ·
    have h2' : (C.u : k) ^ 2 = 1 :=
      val_u_pow_eq_one_of_smul_eq W C hC 2
        (by rw [WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728
          h2 h3 W hj0 hj1728])
    exact pow_eq_one_of_pow_eq_one_of_dvd _ 2 _ h2' (by omega)

end S_WeierstrassCurve_VariableChange_u_pow_add_one_eq_one_of_smul_eq_of_map_j_mem_ssJSet
end P2MW
export P2MW.S_WeierstrassCurve_VariableChange_u_pow_add_one_eq_one_of_smul_eq_of_map_j_mem_ssJSet (solution)

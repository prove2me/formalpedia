-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_tateCurve_galois_signBehavior_of_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/2c1632e3-76ed-5c15-ba43-5bbededea759

import Mathlib
import Definitions.Def_TateCurve_TateParameter
import Theorems.Thm_WeierstrassCurve_exists_variableChange_map_of_j_eq_of_sq_factored
import Theorems.Thm_TateCurve_nnnorm_twistParam_curve_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_tateCurve_galois_signBehavior_of_stabilizer

open scoped NNReal WeierstrassCurve.Affine
open WeierstrassCurve

theorem solution
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hΔ : W.Δ ≠ 0)
    (hpΔ : (p : ℤ) ∣ W.Δ) (hpc₄ : ¬ (p : ℤ) ∣ W.c₄)
    (qT : ℚ_[p]) (hqT0 : qT ≠ 0) (hqT1 : ‖qT‖₊ < 1)
    (hj : (TateCurve.curve qT).c₄ ^ 3
        = (((W.map (Int.castRingHom ℚ)).c₄ ^ 3 / (W.map (Int.castRingHom ℚ)).Δ : ℚ) : ℚ_[p])
            * (TateCurve.curve qT).Δ)
    (hstab : ∀ D : VariableChange (AlgebraicClosure ℚ_[p]),
        D • ((TateCurve.curve qT).map (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])))
          = (TateCurve.curve qT).map (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])) →
        D = 1 ∨ D = (⟨-1, 0, -1, 0⟩ : VariableChange (AlgebraicClosure ℚ_[p]))) :
    ∃ (d : ℚ_[p]), ‖d‖₊ = 1 ∧
      ∃ (s : AlgebraicClosure ℚ_[p]), s ^ 2 = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) d ∧
        ∃ C : VariableChange (AlgebraicClosure ℚ_[p]),
          C • ((W.map (Int.castRingHom ℚ_[p])).map (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])))
            = (TateCurve.curve qT).map (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])) ∧
          ∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
            (σ s = s → C.map σ.toAlgHom.toRingHom = C) ∧
            (σ s ≠ s → C.map σ.toAlgHom.toRingHom
              = (⟨-1, 0, -1, 0⟩ : VariableChange (AlgebraicClosure ℚ_[p])) * C) := by
  set E : WeierstrassCurve ℚ_[p] := W.map (Int.castRingHom ℚ_[p]) with hE
  set E' : WeierstrassCurve ℚ_[p] := TateCurve.curve qT with hE'
  set f : ℚ_[p] →+* AlgebraicClosure ℚ_[p] := algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) with hf
  have h2 : (2 : ℚ_[p]) ≠ 0 := two_ne_zero
  have h3 : (3 : ℚ_[p]) ≠ 0 := three_ne_zero
  have hEc₄ : E.c₄ = (W.c₄ : ℚ_[p]) := by simp only [hE, map_c₄, Int.coe_castRingHom]
  have hEΔ : E.Δ = (W.Δ : ℚ_[p]) := by simp only [hE, map_Δ, Int.coe_castRingHom]
  have hEΔne : E.Δ ≠ 0 := by rw [hEΔ]; exact_mod_cast hΔ
  have hnc₄ : ‖E.c₄‖₊ = 1 := by
    rw [← NNReal.coe_inj, NNReal.coe_one, coe_nnnorm, hEc₄]
    refine le_antisymm (Padic.norm_int_le_one _) (not_lt.mp fun hlt => ?_)
    exact hpc₄ ((Padic.norm_intCast_lt_one_iff (p := p)).mp hlt)
  have hnΔ : ‖E.Δ‖₊ < 1 := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_one, coe_nnnorm, hEΔ]
    exact (Padic.norm_intCast_lt_one_iff (p := p)).mpr hpΔ
  haveI : E.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hEΔne⟩
  haveI : E'.IsElliptic := TateCurve.isElliptic hqT0 hqT1
  have hE'Δne : E'.Δ ≠ 0 := TateCurve.Δ_ne_zero hqT0 hqT1

  have hjE : E.j * E.Δ = E.c₄ ^ 3 := by
    conv_lhs => rw [← E.coe_Δ', WeierstrassCurve.j]
    rw [mul_right_comm, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have hjE' : E'.j * E'.Δ = E'.c₄ ^ 3 := by
    conv_lhs => rw [← E'.coe_Δ', WeierstrassCurve.j]
    rw [mul_right_comm, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

  have hjcross : E'.c₄ ^ 3 * E.Δ = E.c₄ ^ 3 * E'.Δ := by
    have hQ : (((W.map (Int.castRingHom ℚ)).c₄ ^ 3 / (W.map (Int.castRingHom ℚ)).Δ : ℚ) : ℚ_[p])
        = E.c₄ ^ 3 / E.Δ := by
      simp only [map_c₄, map_Δ, Int.coe_castRingHom, hEc₄, hEΔ]; push_cast; ring
    rw [hE', hj, hQ, div_mul_eq_mul_div, div_mul_cancel₀ _ hEΔne]
  have heq : E.j = E'.j := by
    have key : E.j * (E.Δ * E'.Δ) = E'.j * (E.Δ * E'.Δ) := by
      calc E.j * (E.Δ * E'.Δ) = E.c₄ ^ 3 * E'.Δ := by rw [← mul_assoc, hjE]
        _ = E'.c₄ ^ 3 * E.Δ := hjcross.symm
        _ = E'.j * (E.Δ * E'.Δ) := by rw [mul_comm E.Δ, ← mul_assoc, hjE']
    exact mul_right_cancel₀ (mul_ne_zero hEΔne hE'Δne) key

  have hjnorm : 1 < ‖E.j‖₊ := by
    have hΔpos : (0:ℝ≥0) < ‖E.Δ‖₊ := nnnorm_pos.mpr hEΔne
    have hprod : ‖E.j‖₊ * ‖E.Δ‖₊ = 1 := by
      rw [← nnnorm_mul, hjE, nnnorm_pow, hnc₄, one_pow]
    by_contra hle
    push_neg at hle
    have : (1:ℝ≥0) * ‖E.Δ‖₊ < 1 := by
      calc (1:ℝ≥0) * ‖E.Δ‖₊ = ‖E.Δ‖₊ := one_mul _
        _ < 1 := hnΔ
    have : ‖E.j‖₊ * ‖E.Δ‖₊ < 1 :=
      lt_of_le_of_lt (mul_le_mul_left hle _) this
    exact absurd hprod (ne_of_lt this)
  have hj0 : E.j ≠ 0 := fun h => by simp [h] at hjnorm
  have hj1728 : E.j ≠ 1728 := fun h => by
    have : ‖E.j‖₊ ≤ 1 := by
      rw [h]; exact_mod_cast IsUltrametricDist.nnnorm_natCast_le_one ℚ_[p] 1728
    exact absurd this (not_le.mpr hjnorm)

  set d : ℚ_[p] := E.c₆ * E'.c₄ / (E'.c₆ * E.c₄) with hd
  have hdnorm : ‖d‖₊ = 1 := by
    rw [hd, hE']
    exact TateCurve.nnnorm_twistParam_curve_eq_one E hnc₄ hnΔ hqT0 hqT1

  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (f d) (n := 2) (by norm_num)

  obtain ⟨A, B, hs0, hCeq⟩ :=
    WeierstrassCurve.exists_variableChange_map_of_j_eq_of_sq_factored f h2 h3 E E' heq hj0 hj1728
      (s := s) (by rw [hs, hd])
  refine ⟨d, hdnorm, s, hs, (A.map f) * (⟨Units.mk0 s hs0, 0, 0, 0⟩ : VariableChange _) * (B.map f),
    hCeq, ?_⟩
  intro σ

  have hσf : (σ.toAlgHom.toRingHom).comp f = f := by
    ext x; exact σ.commutes x
  have hσA : (A.map f).map σ.toAlgHom.toRingHom = A.map f := by
    rw [VariableChange.map_map, hσf]
  have hσB : (B.map f).map σ.toAlgHom.toRingHom = B.map f := by
    rw [VariableChange.map_map, hσf]

  have hmh : ∀ X : VariableChange (AlgebraicClosure ℚ_[p]),
      X.map σ.toAlgHom.toRingHom = (VariableChange.mapHom σ.toAlgHom.toRingHom) X := fun _ => rfl

  have hσmid : ((⟨Units.mk0 s hs0, 0, 0, 0⟩ : VariableChange _).map σ.toAlgHom.toRingHom)
      = (⟨Units.map (σ.toAlgHom.toRingHom : _ →* _) (Units.mk0 s hs0), 0, 0, 0⟩ : VariableChange _) := by
    ext <;> simp [VariableChange.map]

  set C : VariableChange (AlgebraicClosure ℚ_[p]) :=
    (A.map f) * (⟨Units.mk0 s hs0, 0, 0, 0⟩ : VariableChange _) * (B.map f) with hC
  have hσC : C.map σ.toAlgHom.toRingHom
      = (A.map f) * (⟨Units.map (σ.toAlgHom.toRingHom : _ →* _) (Units.mk0 s hs0), 0, 0, 0⟩
          : VariableChange _) * (B.map f) := by
    rw [hC, hmh, map_mul, map_mul, ← hmh, ← hmh, ← hmh, hσA, hσB, hσmid]
  have hσs2 : (σ s) ^ 2 = s ^ 2 := by
    calc (σ s) ^ 2 = σ (s ^ 2) := (map_pow σ s 2).symm
      _ = σ (f d) := by rw [hs]
      _ = f d := σ.commutes d
      _ = s ^ 2 := hs.symm
  constructor
  ·
    intro hσs
    rw [hσC, hC]
    congr 2
    refine VariableChange.ext (Units.ext ?_) rfl rfl rfl
    exact hσs
  ·
    intro hσs
    have hσsneg : σ s = -s := by
      have hprod : (σ s - s) * (σ s + s) = 0 := by
        have hfac : (σ s - s) * (σ s + s) = (σ s) ^ 2 - s ^ 2 := by ring
        rw [hfac, hσs2, sub_self]
      rcases mul_eq_zero.mp hprod with h | h
      · exact absurd (sub_eq_zero.mp h) hσs
      · exact eq_neg_of_add_eq_zero_left h

    have hmid_fact :
        (⟨Units.map (σ.toAlgHom.toRingHom : _ →* _) (Units.mk0 s hs0), 0, 0, 0⟩
            : VariableChange (AlgebraicClosure ℚ_[p]))
          = (⟨-1, 0, 0, 0⟩ : VariableChange _) * ⟨Units.mk0 s hs0, 0, 0, 0⟩ := by
      refine VariableChange.ext (Units.ext ?_) ?_ ?_ ?_
      · simp only [VariableChange.mul_def, Units.val_mul, Units.coe_map, MonoidHom.coe_coe,
          Units.val_mk0, Units.val_neg, Units.val_one]
        exact hσsneg.trans (neg_one_mul s).symm
      all_goals simp [VariableChange.mul_def]

    set D : VariableChange (AlgebraicClosure ℚ_[p]) :=
      (A.map f) * (⟨-1, 0, 0, 0⟩ : VariableChange _) * (A.map f)⁻¹ with hD
    have hσC_eq : C.map σ.toAlgHom.toRingHom = D * C := by
      rw [hσC, hmid_fact, hD, hC]; group

    have hDstab : D • (E'.map f) = E'.map f := by
      have hEmap_fix : (E.map f).map σ.toAlgHom.toRingHom = E.map f := by
        rw [WeierstrassCurve.map_map, hσf]
      have hE'map_fix : (E'.map f).map σ.toAlgHom.toRingHom = E'.map f := by
        rw [WeierstrassCurve.map_map, hσf]
      have key : (C.map σ.toAlgHom.toRingHom) • (E.map f) = E'.map f := by
        calc (C.map σ.toAlgHom.toRingHom) • (E.map f)
            = (C.map σ.toAlgHom.toRingHom) • ((E.map f).map σ.toAlgHom.toRingHom) := by
              rw [hEmap_fix]
          _ = (C • (E.map f)).map σ.toAlgHom.toRingHom := map_variableChange _ _ _
          _ = (E'.map f).map σ.toAlgHom.toRingHom := by rw [hCeq]
          _ = E'.map f := hE'map_fix
      calc D • (E'.map f) = D • (C • (E.map f)) := by rw [← hCeq]
        _ = (D * C) • (E.map f) := (mul_smul D C (E.map f)).symm
        _ = (C.map σ.toAlgHom.toRingHom) • (E.map f) := by rw [← hσC_eq]
        _ = E'.map f := key

    have hDu : D.u = -1 := by
      have hDu' : D.u = (A.map f).u * (-1) * ((A.map f).u)⁻¹ := by
        rw [hD, VariableChange.mul_def, VariableChange.mul_def, VariableChange.inv_def]
      rw [hDu', mul_comm ((A.map f).u) (-1), mul_assoc, mul_inv_cancel, mul_one]

    have hDι : D = (⟨-1, 0, -1, 0⟩ : VariableChange _) := by
      rcases hstab D hDstab with h1 | hι
      · exfalso
        have hu1 : D.u = 1 := by rw [h1, VariableChange.one_def]
        rw [hDu] at hu1
        have hK : (-1 : AlgebraicClosure ℚ_[p]) = 1 := by
          have := Units.ext_iff.mp hu1
          simpa [Units.val_neg, Units.val_one] using this
        exact (two_ne_zero : (2 : AlgebraicClosure ℚ_[p]) ≠ 0) (by linear_combination -hK)
      · exact hι
    rw [hσC_eq, hDι]

end S_WeierstrassCurve_exists_variableChange_tateCurve_galois_signBehavior_of_stabilizer
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_tateCurve_galois_signBehavior_of_stabilizer (solution)

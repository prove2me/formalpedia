-- Prove2me | solution 1 for PrimeLocal.exists_tate_sign_data_of_nonintegral_j
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T00:03:05.983063+00:00
-- url     : https://prove2.me/submissions/3aa950b5-24ec-4a93-8c01-c067d80bdcb9

import Mathlib
import Theorems.Thm_WeierstrassCurve_exists_variableChange_map_of_j_eq_of_sq_factored
import Theorems.Thm_WeierstrassCurve_variableChange_smul_eq_self_iff_of_tateNormalForm
import Theorems.Thm_TateCurve_nnnorm_c_six
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine
import Definitions.Def_TateCurve_TateParameter

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine NNReal
universe u v

namespace PrimeLocal
theorem _root_.solution (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (q : ℕ) [Fact q.Prime] (hj : ¬ ((q : ℤ) ^ padicValInt q W.Δ ∣ W.c₄ ^ 3)) : ∃ (qT : ℚ_[q]) (_ : qT ≠ 0) (_ : ‖qT‖₊ < 1) (d : ℚ_[q]) (s : AlgebraicClosure ℚ_[q]) (C : WeierstrassCurve.VariableChange (AlgebraicClosure ℚ_[q])), s ^ 2 = algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q]) d ∧ C • ((W.map (Int.castRingHom ℚ_[q])).map (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q]))) = (TateCurve.curve qT).map (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])) ∧ ∀ σ : AlgebraicClosure ℚ_[q] ≃ₐ[ℚ_[q]] AlgebraicClosure ℚ_[q], (σ s = s → C.map σ.toAlgHom.toRingHom = C) ∧ (σ s ≠ s → C.map σ.toAlgHom.toRingHom = (⟨-1, 0, -1, 0⟩ : WeierstrassCurve.VariableChange (AlgebraicClosure ℚ_[q])) * C) := by
  classical
  let E : WeierstrassCurve ℚ_[q] := W.map (Int.castRingHom ℚ_[q])
  have hEΔ : E.Δ = (W.Δ : ℚ_[q]) := by simp [E]
  have hEΔne : E.Δ ≠ 0 := by rw [hEΔ]; exact_mod_cast hΔ
  letI : E.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hEΔne⟩
  have hjnorm : 1 < ‖E.j‖₊ := by
    have hΔnorm : ‖(W.Δ : ℚ_[q])‖ = (q : ℝ) ^ (-(padicValInt q W.Δ : ℤ)) := by
      rw [show (W.Δ : ℚ_[q]) = ((W.Δ : ℚ) : ℚ_[q]) by norm_cast,
        Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hΔ),
        padicValRat.of_int]
      push_cast
      rfl
    have hlt : ‖(W.Δ : ℚ_[q])‖ < ‖((W.c₄ ^ 3 : ℤ) : ℚ_[q])‖ := by
      rw [hΔnorm]
      exact lt_of_not_ge (fun h => hj ((Padic.norm_int_le_pow_iff_dvd _ _).mp h))
    have hjprod : E.j * E.Δ = E.c₄ ^ 3 := by
      conv_lhs => rw [← E.coe_Δ', WeierstrassCurve.j]
      rw [mul_right_comm, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    have hlt' : ‖E.Δ‖ < ‖E.j‖ * ‖E.Δ‖ := by
      rw [← norm_mul, hjprod]
      simpa [E] using hlt
    have hreal : 1 < ‖E.j‖ := by nlinarith [norm_pos_iff.mpr hEΔne]
    exact_mod_cast hreal
  obtain ⟨qT, hqT0, hqT1, _, hjT⟩ := TateCurve.exists_tateParameter_of_isElliptic E hjnorm
  let E' : WeierstrassCurve ℚ_[q] := TateCurve.curve qT
  let f : ℚ_[q] →+* AlgebraicClosure ℚ_[q] := algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])
  letI : E'.IsElliptic := TateCurve.isElliptic hqT0 hqT1
  have heq : E.j = E'.j := hjT.symm
  have h2 : (2 : ℚ_[q]) ≠ 0 := two_ne_zero
  have h3 : (3 : ℚ_[q]) ≠ 0 := three_ne_zero
  have hj0 : E.j ≠ 0 := fun h => by simp [h] at hjnorm
  have hj1728 : E.j ≠ 1728 := fun h => by
    have : ‖E.j‖₊ ≤ 1 := by
      rw [h]; exact_mod_cast IsUltrametricDist.nnnorm_natCast_le_one ℚ_[q] 1728
    exact absurd this (not_le.mpr hjnorm)
  have hstab : ∀ D : VariableChange (AlgebraicClosure ℚ_[q]),
      D • E'.map f = E'.map f →
      D = 1 ∨ D = (⟨-1, 0, -1, 0⟩ : VariableChange _) := by
    intro D hD
    apply (WeierstrassCurve.variableChange_smul_eq_self_iff_of_tateNormalForm
      (E'.map f) (by simp [E', TateCurve.curve]) (by simp [E', TateCurve.curve])
      (by simp [E', TateCurve.curve]) ?_ ?_ D).mp hD
    · rw [map_c₄]; apply (map_ne_zero f).mpr
      exact nnnorm_pos.mp (by simp [E', TateCurve.nnnorm_c₄ hqT1])
    · rw [map_c₆]; apply (map_ne_zero f).mpr
      intro hzero
      have hc := TateCurve.nnnorm_c_six hqT1
      rw [show (TateCurve.curve qT).c₆ = 0 from hzero, nnnorm_zero] at hc
      exact zero_ne_one hc
  set d : ℚ_[q] := E.c₆ * E'.c₄ / (E'.c₆ * E.c₄) with hd
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (f d) (n := 2) (by norm_num)

  obtain ⟨A, B, hs0, hCeq⟩ :=
    WeierstrassCurve.exists_variableChange_map_of_j_eq_of_sq_factored f h2 h3 E E' heq hj0 hj1728
      (s := s) (by rw [hs, hd])
  refine ⟨qT, hqT0, hqT1, d, s,
    (A.map f) * (⟨Units.mk0 s hs0, 0, 0, 0⟩ : VariableChange _) * (B.map f),
    hs, hCeq, ?_⟩
  intro σ

  have hσf : (σ.toAlgHom.toRingHom).comp f = f := by
    ext x; exact σ.commutes x
  have hσA : (A.map f).map σ.toAlgHom.toRingHom = A.map f := by
    rw [VariableChange.map_map, hσf]
  have hσB : (B.map f).map σ.toAlgHom.toRingHom = B.map f := by
    rw [VariableChange.map_map, hσf]

  have hmh : ∀ X : VariableChange (AlgebraicClosure ℚ_[q]),
      X.map σ.toAlgHom.toRingHom = (VariableChange.mapHom σ.toAlgHom.toRingHom) X := fun _ => rfl

  have hσmid : ((⟨Units.mk0 s hs0, 0, 0, 0⟩ : VariableChange _).map σ.toAlgHom.toRingHom)
      = (⟨Units.map (σ.toAlgHom.toRingHom : _ →* _) (Units.mk0 s hs0), 0, 0, 0⟩ : VariableChange _) := by
    ext <;> simp [VariableChange.map]

  set C : VariableChange (AlgebraicClosure ℚ_[q]) :=
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
            : VariableChange (AlgebraicClosure ℚ_[q]))
          = (⟨-1, 0, 0, 0⟩ : VariableChange _) * ⟨Units.mk0 s hs0, 0, 0, 0⟩ := by
      refine VariableChange.ext (Units.ext ?_) ?_ ?_ ?_
      · simp only [VariableChange.mul_def, Units.val_mul, Units.coe_map, MonoidHom.coe_coe,
          Units.val_mk0, Units.val_neg, Units.val_one]
        exact hσsneg.trans (neg_one_mul s).symm
      all_goals simp [VariableChange.mul_def]

    set D : VariableChange (AlgebraicClosure ℚ_[q]) :=
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
        have hK : (-1 : AlgebraicClosure ℚ_[q]) = 1 := by
          have := Units.ext_iff.mp hu1
          simpa [Units.val_neg, Units.val_one] using this
        exact (two_ne_zero : (2 : AlgebraicClosure ℚ_[q]) ≠ 0) (by linear_combination -hK)
      · exact hι
    rw [hσC_eq, hDι]


end PrimeLocal

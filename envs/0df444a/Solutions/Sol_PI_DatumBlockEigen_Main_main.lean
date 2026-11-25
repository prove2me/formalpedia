-- Prove2me | solution 1 for PI.DatumBlockEigen.Main.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:39:59.839608+00:00
-- url     : https://prove2.me/submissions/37945d55-3973-46dc-8dee-f5eb26ac02f9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DatumBlockEigen
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LemmaU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_IsIntInvOfUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_PhiUZero
import Theorems.Thm_PI_DatumBlockEigen_Main_phiU_of
import Theorems.Thm_PI_DatumBlockEigen_Main_phiU_zero
import Theorems.Thm_PI_DatumBlockEigen_Main_good_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
namespace PI.DatumBlockEigen.Main
open PI.DatumBlockEigen.Unit Formalism.DoubleCosetMeasures
section
variable {F : Type} [Field F] {a t : ℕ}
variable (O : Subring F) (ϖ : F) (J' : Subgroup (GL (Fin a) F))
variable {O ϖ J'}
private lemma mul_entries_mem_of_entries_mem {m n p : Type*} [Fintype n] {P : Matrix m n F} {Q : Matrix n p F}
    (hP : ∀ i j, P i j ∈ O) (hQ : ∀ i j, Q i j ∈ O) : ∀ i j, (P * Q) i j ∈ O := by
  intro i j
  rw [Matrix.mul_apply]
  exact O.sum_mem (fun l _ => O.mul_mem (hP i l) (hQ l j))
private lemma mem_IIset_iff_inv_smul_entries_mem (hϖ0 : ϖ ≠ 0) {p q : ℕ} (y : Matrix (Fin p) (Fin q) F) :
    y ∈ IIset O ϖ ↔ ∀ i j, (ϖ⁻¹ • y) i j ∈ O := by
  show (∀ i j, ∃ o ∈ O, y i j = ϖ * o) ↔ _
  constructor
  · intro h i j
    obtain ⟨o, ho, he⟩ := h i j
    rw [Matrix.smul_apply, he, smul_eq_mul, inv_mul_cancel_left₀ hϖ0]
    exact ho
  · intro h i j
    refine ⟨ϖ⁻¹ * y i j, h i j, ?_⟩
    rw [mul_inv_cancel_left₀ hϖ0]
private lemma exists_mem_congSub_eq_one_add_smul (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0) (hL : IsLocalAt O ϖ)
    (Y : Matrix (Fin a) (Fin a) F) (hY : IsInt O Y) :
    ∃ U : GL (Fin a) F, U ∈ congSub O ϖ a ∧ (U : Matrix (Fin a) (Fin a) F) = 1 + ϖ • Y := by
  classical
  let w : O := ⟨ϖ, hϖ⟩
  let YO : Matrix (Fin a) (Fin a) O := fun i j => ⟨Y i j, hY i j⟩
  let UO : Matrix (Fin a) (Fin a) O := 1 + w • YO
  have hmap : O.subtype.mapMatrix UO = 1 + ϖ • Y := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [UO, YO, w]
      rfl
    · simp [UO, YO, w, Matrix.one_apply_ne hij]
      rfl
  let I : Ideal O := Ideal.span {w}
  have hw : Ideal.Quotient.mk I w = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hred : (Ideal.Quotient.mk I).mapMatrix UO = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [UO, hw]
    · simp [UO, hw, Matrix.one_apply_ne hij]
  have hdet : UO.det - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, RingHom.map_det, hred, Matrix.det_one,
      sub_self]
  obtain ⟨o, ho⟩ := Ideal.mem_span_singleton'.mp hdet
  have h1 : (o : F) * ϖ = (UO.det : F) - 1 := by
    have := congrArg (fun r : O => (r : F)) ho
    simpa [w] using this
  have hdetmap : (1 + ϖ • Y).det = (UO.det : F) := by
    rw [← hmap, ← RingHom.map_det]
    rfl
  have hnd : ∀ o' ∈ O, (UO.det : F) ≠ ϖ * o' := by
    intro o' ho' heq
    apply hL.1
    have h2 : ϖ * (o' - (o : F)) = 1 := by linear_combination -h1 - heq
    rw [← eq_inv_of_mul_eq_one_right h2]
    exact O.sub_mem ho' o.2
  have hinv : (UO.det : F)⁻¹ ∈ O := hL.2 _ (UO.det).2 hnd
  have hne : (1 + ϖ • Y).det ≠ 0 := by
    rw [hdetmap]
    intro h0
    exact hnd 0 O.zero_mem (by rw [h0, mul_zero])
  let U0 : GL (Fin a) F := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hne
  have hU0 : (U0 : Matrix (Fin a) (Fin a) F) = 1 + ϖ • Y := rfl
  have hU0i : ((U0⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = (1 + ϖ • Y)⁻¹ := by
    rw [Matrix.coe_units_inv, hU0]
  have hG : U0 ∈ GLint O a := by
    show IsInt O _ ∧ IsInt O _
    refine ⟨?_, ?_⟩
    · rw [hU0, ← hmap]
      exact fun i j => (UO i j).2
    · rw [hU0i, Matrix.inv_def, Ring.inverse_eq_inv', hdetmap, ← hmap, ← RingHom.map_adjugate]
      intro i j
      rw [Matrix.smul_apply, smul_eq_mul]
      exact O.mul_mem hinv (UO.adjugate i j).2
  refine ⟨U0, ?_, rfl⟩
  show U0 ∈ GLint O a ∧ _
  refine ⟨hG, ?_⟩
  rw [hU0, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hϖ0, one_smul]
  exact hY
end
end PI.DatumBlockEigen.Main
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.DatumBlockEigen PI.DatumBlockEigen.Main
open PI.DatumBlockEigen.Unit Formalism.DoubleCosetMeasures
namespace PI.DatumBlockEigen.Main
theorem _root_.solution : PI.DatumBlockEigen := by
  unfold PI.DatumBlockEigen
  intro F _ O ϖ hϖ hϖ0 hL a t J' hK hJ ρ hρ h hb
  unfold PI.DatumBlockEigen.blockCond at hb
  dsimp only at hb ⊢
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F,
      M = reindex finSumFinEquiv.symm finSumFinEquiv.symm
        (h : Matrix (Fin (a + t)) (Fin (a + t)) F) := ⟨_, rfl⟩
  obtain ⟨Mi, hMi⟩ : ∃ Mi : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F,
      Mi = reindex finSumFinEquiv.symm finSumFinEquiv.symm
        ((h⁻¹ : GL (Fin (a + t)) F) : Matrix (Fin (a + t)) (Fin (a + t)) F) := ⟨_, rfl⟩
  rw [← hM] at hb
  rw [← hMi]
  obtain ⟨⟨k, hkJ, hkA⟩, hBint, hCII, D0, hD0, hDD⟩ := hb
  have hMMi : M * Mi = 1 := by
    rw [hM, hMi, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.submatrix_one_equiv]
  obtain ⟨A, hA⟩ : ∃ A, A = M.toBlocks₁₁ := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = M.toBlocks₁₂ := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = M.toBlocks₂₁ := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = M.toBlocks₂₂ := ⟨_, rfl⟩
  have hMb : M = fromBlocks A B C D := by
    rw [hA, hB, hC, hD, Matrix.fromBlocks_toBlocks]
  rw [← hA] at hkA
  rw [← hB] at hBint
  rw [← hC] at hCII
  rw [← hD] at hDD
  have hkint : IsInt O (k : Matrix (Fin a) (Fin a) F) ∧
      IsInt O ((k⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) := hJ hkJ
  have hDint : IsInt O (D0 : Matrix (Fin t) (Fin t) F) ∧
      IsInt O ((D0⁻¹ : GL (Fin t) F) : Matrix (Fin t) (Fin t) F) := hD0
  have hC' := (mem_IIset_iff_inv_smul_entries_mem hϖ0 C).mp hCII
  obtain ⟨Ai, hAi⟩ : ∃ Ai : Matrix (Fin a) (Fin a) F,
      Ai = ((k⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) := ⟨_, rfl⟩
  have hAAi : A * Ai = 1 := by
    rw [← hkA, hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAiint : ∀ i j, Ai i j ∈ O := by
    rw [hAi]
    exact hkint.2
  obtain ⟨Di, hDi⟩ : ∃ Di : Matrix (Fin t) (Fin t) F,
      Di = ((D0⁻¹ : GL (Fin t) F) : Matrix (Fin t) (Fin t) F) := ⟨_, rfl⟩
  have hDDi : D * Di = 1 := by
    rw [← hDD, hDi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hDiint : ∀ i j, Di i j ∈ O := by
    rw [hDi]
    exact hDint.2
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix (Fin t) (Fin t) F, Y = -(Di * ((ϖ⁻¹ • C) * (Ai * B))) := ⟨_, rfl⟩
  have hYint : IsInt O Y := by
    intro i j
    rw [hY, Matrix.neg_apply]
    exact O.neg_mem (mul_entries_mem_of_entries_mem hDiint (mul_entries_mem_of_entries_mem hC' (mul_entries_mem_of_entries_mem hAiint hBint)) i j)
  obtain ⟨U, hU, hUc⟩ := exists_mem_congSub_eq_one_add_smul (a := t) hϖ hϖ0 hL Y hYint
  have hUG : U ∈ GLint O t := (hU : U ∈ GLint O t ∧ _).1
  have hDY : D * Y = -((ϖ⁻¹ • C) * (Ai * B)) := by
    rw [hY, Matrix.mul_neg, ← Matrix.mul_assoc D Di, hDDi, Matrix.one_mul]
  have hS : ((D0 * U : GL (Fin t) F) : Matrix (Fin t) (Fin t) F) = D - C * Ai * B := by
    rw [Units.val_mul, hUc, hDD, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hDY,
      Matrix.smul_mul, smul_neg, smul_smul, mul_inv_cancel₀ hϖ0, one_smul, ← Matrix.mul_assoc,
      sub_eq_add_neg]
  have hSG : IsInt O ((D0 * U : GL (Fin t) F) : Matrix (Fin t) (Fin t) F) ∧
      IsInt O (((D0 * U)⁻¹ : GL (Fin t) F) : Matrix (Fin t) (Fin t) F) :=
    (GLint O t).mul_mem hD0 hUG
  obtain ⟨Si, hSi⟩ : ∃ Si : Matrix (Fin t) (Fin t) F,
      Si = (((D0 * U)⁻¹ : GL (Fin t) F) : Matrix (Fin t) (Fin t) F) := ⟨_, rfl⟩
  have hSSi : (D - C * Ai * B) * Si = 1 := by
    rw [← hS, hSi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hSiint : ∀ i j, Si i j ∈ O := by
    rw [hSi]
    exact hSG.2
  have hDSi : D * Si = 1 + C * Ai * B * Si := by
    have e : D = (D - C * Ai * B) + C * Ai * B := by abel
    rw [e, Matrix.add_mul, hSSi]
  have hMX : M * fromBlocks (Ai + Ai * B * Si * (C * Ai)) (-(Ai * B * Si)) (-(Si * (C * Ai))) Si
      = 1 := by
    rw [hMb, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    congr 1
    · simp only [Matrix.mul_add, Matrix.mul_neg, ← Matrix.mul_assoc, hAAi, Matrix.one_mul]
      abel
    · simp only [Matrix.mul_neg, ← Matrix.mul_assoc, hAAi, Matrix.one_mul]
      abel
    · simp only [Matrix.mul_add, Matrix.mul_neg, ← Matrix.mul_assoc, hDSi, Matrix.add_mul,
        Matrix.one_mul]
      abel
    · simp only [Matrix.mul_neg, ← Matrix.mul_assoc, hDSi]
      abel
  have hMiX : Mi = fromBlocks (Ai + Ai * B * Si * (C * Ai)) (-(Ai * B * Si)) (-(Si * (C * Ai))) Si := by
    rw [← Matrix.inv_eq_right_inv hMMi, Matrix.inv_eq_right_inv hMX]
  have hEII : ∀ i j, (ϖ⁻¹ • (C * Ai)) i j ∈ O := by
    rw [← Matrix.smul_mul]
    exact mul_entries_mem_of_entries_mem hC' hAiint
  obtain ⟨U2, hU2, hU2c⟩ := exists_mem_congSub_eq_one_add_smul (a := a) hϖ hϖ0 hL (B * Si * (ϖ⁻¹ • (C * Ai)))
    (mul_entries_mem_of_entries_mem (mul_entries_mem_of_entries_mem hBint hSiint) hEII)
  have hk'coe : (((⟨k⁻¹ * U2, J'.mul_mem (J'.inv_mem hkJ) (hK hU2)⟩ : J') : GL (Fin a) F) :
      Matrix (Fin a) (Fin a) F) = Mi.toBlocks₁₁ := by
    rw [hMiX, Matrix.toBlocks_fromBlocks₁₁]
    show ((k⁻¹ * U2 : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = _
    rw [Units.val_mul, ← hAi, hU2c]
    simp only [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hϖ0,
      one_smul, ← Matrix.mul_assoc]
  have h12 : ∀ i j, Mi.toBlocks₁₂ i j ∈ O := by
    rw [hMiX, Matrix.toBlocks_fromBlocks₁₂]
    intro i j
    rw [Matrix.neg_apply]
    exact O.neg_mem (mul_entries_mem_of_entries_mem (mul_entries_mem_of_entries_mem hAiint hBint) hSiint i j)
  have h21 : Mi.toBlocks₂₁ ∈ IIset O ϖ := by
    rw [hMiX, Matrix.toBlocks_fromBlocks₂₁]
    apply (mem_IIset_iff_inv_smul_entries_mem hϖ0 _).mpr
    rw [smul_neg, ← Matrix.mul_smul]
    intro i j
    rw [Matrix.neg_apply]
    exact O.neg_mem (mul_entries_mem_of_entries_mem hSiint hEII i j)
  have h22 : ∀ i j, Mi.toBlocks₂₂ i j ∈ O := by
    rw [hMiX, Matrix.toBlocks_fromBlocks₂₂]
    exact hSiint
  refine ⟨⟨k⁻¹ * U2, J'.mul_mem (J'.inv_mem hkJ) (hK hU2)⟩, hk'coe, fun x => ?_⟩
  by_cases hs : Supp O ϖ J' x
  · obtain ⟨⟨m, hm⟩, hx⟩ := hs
    obtain ⟨g, hg, hg2, U3, hU3, hgeq⟩ :=
      good_mul hϖ hϖ0 hL hK hJ Mi _ hk'coe h12 h21 h22 x m hm hx
    rw [phiU_of O ϖ J' ρ (Mi * x) g hg hg2, phiU_of O ϖ J' ρ x m hm hx, hgeq, map_mul, map_mul,
      hρ U3 hU3, mul_one, Units.val_mul]
  · rw [phiU_zero O ϖ J' ρ x hs, mul_zero]
    apply phiU_zero O ϖ J' ρ (Mi * x)
    rintro ⟨⟨m, hm⟩, hx⟩
    apply hs
    have hMx : M * (Mi * x) = x := by
      rw [← Matrix.mul_assoc, hMMi, Matrix.one_mul]
    obtain ⟨g, hg, hg2, -⟩ := good_mul hϖ hϖ0 hL hK hJ M ⟨k, hkJ⟩ (hkA.trans hA)
      (by rw [← hB]; exact hBint) (by rw [← hC]; exact hCII)
      (by rw [← hD, ← hDD]; exact hDint.1) (Mi * x) m hm hx
    rw [hMx] at hg hg2
    exact ⟨⟨g, hg⟩, hg2⟩
end PI.DatumBlockEigen.Main

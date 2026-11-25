-- Prove2me | solution 1 for PI.DatumBlockEigen.Main.good_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:35:06.466802+00:00
-- url     : https://prove2.me/submissions/c8218363-1f24-463f-8e0d-3afcfd6be70a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DatumBlockEigen
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LemmaU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_IsIntInvOfUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_PhiUZero
import Theorems.Thm_P2M_PI_DatumBlockEigen_Main_toRows__mul__1fa7e55c80c1
import Theorems.Thm_P2M_PI_DatumBlockEigen_Main_toRows__mul__b0adba7dcda3
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
variable {F : Type} [Field F] {a t : ℕ}
variable (O : Subring F) (ϖ : F) (J' : Subgroup (GL (Fin a) F))
variable {O ϖ J'}
namespace PI.DatumBlockEigen.Main
theorem _root_.solution (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0) (hL : IsLocalAt O ϖ) (hK : congSub O ϖ a ≤ J')
    (hJ : J' ≤ GLint O a) (N : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F) (n : J')
    (hn : ((n : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = N.toBlocks₁₁)
    (h12 : ∀ i j, N.toBlocks₁₂ i j ∈ O) (h21 : N.toBlocks₂₁ ∈ IIset O ϖ)
    (h22 : ∀ i j, N.toBlocks₂₂ i j ∈ O) (x : Matrix (Fin a ⊕ Fin t) (Fin a) F) (m : J')
    (hm : ((m : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = toRows₁ x)
    (hx : toRows₂ x ∈ IIset O ϖ) :
    ∃ g : J', ((g : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = toRows₁ (N * x) ∧
      toRows₂ (N * x) ∈ IIset O ϖ ∧
      ∃ U : J', (U : GL (Fin a) F) ∈ congSub O ϖ a ∧ g = n * m * U := by
  obtain ⟨W, hWdef⟩ : ∃ W : GL (Fin a) F, W = ((n * m : J') : GL (Fin a) F) := ⟨_, rfl⟩
  have hWint : IsInt O (W : Matrix (Fin a) (Fin a) F) ∧ IsInt O ((W⁻¹ : GL (Fin a) F) :
      Matrix (Fin a) (Fin a) F) := by
    rw [hWdef]
    exact hJ (n * m).2
  have hmint : IsInt O ((m : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) ∧
      IsInt O (((m : GL (Fin a) F)⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) := hJ m.2
  have hWcoe : (W : Matrix (Fin a) (Fin a) F) = N.toBlocks₁₁ * toRows₁ x := by
    rw [hWdef, Subgroup.coe_mul, Units.val_mul, hn, hm]
  have hx' := (mem_IIset_iff_inv_smul_entries_mem hϖ0 (toRows₂ x)).mp hx
  have hZ' : ∀ i j, (ϖ⁻¹ • (N.toBlocks₁₂ * toRows₂ x)) i j ∈ O := by
    rw [← Matrix.mul_smul]
    exact mul_entries_mem_of_entries_mem h12 hx'
  obtain ⟨U, hU, hUc⟩ := exists_mem_congSub_eq_one_add_smul hϖ hϖ0 hL
    (((W⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) * (ϖ⁻¹ • (N.toBlocks₁₂ * toRows₂ x)))
    (mul_entries_mem_of_entries_mem hWint.2 hZ')
  have hWW : (W : Matrix (Fin a) (Fin a) F) * ((W⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine ⟨n * m * ⟨U, hK hU⟩, ?_, ?_, ⟨U, hK hU⟩, hU, rfl⟩
  · calc (((n * m * ⟨U, hK hU⟩ : J') : GL (Fin a) F) : Matrix (Fin a) (Fin a) F)
        = (W : Matrix (Fin a) (Fin a) F) * (U : Matrix (Fin a) (Fin a) F) := by
          rw [Subgroup.coe_mul, Units.val_mul, ← hWdef]
      _ = (W : Matrix (Fin a) (Fin a) F) + N.toBlocks₁₂ * toRows₂ x := by
          rw [hUc, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, hWW,
            Matrix.one_mul, smul_smul, mul_inv_cancel₀ hϖ0, one_smul]
      _ = toRows₁ (N * x) := by rw [toRows₁_mul', ← hWcoe]
  · rw [toRows₂_mul']
    apply (mem_IIset_iff_inv_smul_entries_mem hϖ0 _).mpr
    have h21' := (mem_IIset_iff_inv_smul_entries_mem hϖ0 _).mp h21
    rw [smul_add, ← Matrix.smul_mul, ← Matrix.mul_smul]
    intro i j
    exact O.add_mem (mul_entries_mem_of_entries_mem h21' (by rw [← hm]; exact hmint.1) i j)
      (mul_entries_mem_of_entries_mem h22 hx' i j)
end PI.DatumBlockEigen.Main

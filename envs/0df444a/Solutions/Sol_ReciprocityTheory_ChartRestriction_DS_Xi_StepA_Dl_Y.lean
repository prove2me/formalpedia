-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Dl_Y
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:38:30.632179+00:00
-- url     : https://prove2.me/submissions/b3661c09-5cd4-4756-8b10-64aec4c63633

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GoodRowsProjectorApplyEqSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DetEqMulMinorOfColZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_herm_lift_lift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_herm_last_lift_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_herm_last_first_eq_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_det_eq_mul_minor_of_col_zero_alt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_castLE_succ_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_last
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_mp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_zero_pos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_last
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_mp
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_zero_pos


section
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
section lev
variable (k r' : ℕ)
private lemma liftVec_apply_of_edge (u : Fin (2 * r' + k + 1) → ℂ) (i : Fin (2 * (1 + r') + k + 1))
    (hi : i.val = 0 ∨ i.val = 2 * (1 + r') + k) : liftVec k 1 r' u i = 0 := by
  simp only [liftVec]
  split_ifs <;> first | rfl | omega
private lemma liftVec_apply_succ (u : Fin (2 * r' + k + 1) → ℂ) (a : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' u ⟨a.val + 1, by omega⟩ = u a := by
  simp only [liftVec, Fin.val_mk]
  rw [dif_pos (by omega)]
  exact congrArg u (Fin.ext (by show a.val + 1 - 1 = a.val; omega))
private lemma Hpk_one_add_apply_succ_succ (a b : Fin (2 * r' + k + 1)) :
    Hpk k (1 + r') ⟨a.val + 1, by omega⟩ ⟨b.val + 1, by omega⟩ = Hpk k r' a b := by
  simp only [Hpk, Fin.val_mk, Fin.ext_iff]
  split_ifs <;> first | rfl | omega
private lemma sum_eq_sum_succ_of_zero_at_edges (f : Fin (2 * (1 + r') + k + 1) → ℂ)
    (hf : ∀ i : Fin (2 * (1 + r') + k + 1), (i.val = 0 ∨ i.val = 2 * (1 + r') + k) → f i = 0) :
    ∑ i, f i = ∑ a : Fin (2 * r' + k + 1), f ⟨a.val + 1, by omega⟩ := by
  have hinj : Function.Injective
      (fun a : Fin (2 * r' + k + 1) => (⟨a.val + 1, by omega⟩ : Fin (2 * (1 + r') + k + 1))) := by
    intro a b h
    simp only [Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  symm
  apply Fintype.sum_of_injective _ hinj
  · intro i hi
    apply hf
    by_contra hne
    apply hi
    exact ⟨⟨i.val - 1, by omega⟩, Fin.ext (by show i.val - 1 + 1 = i.val; omega)⟩
  · intro a
    rfl
private lemma mulVec_bvec_eq_col_fun {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) :
    H *ᵥ bvec j = fun i => H i j := by
  funext i
  simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]
private lemma phiV'_one_add_zero_eq_first_basis_e0_vec : phiV' k (1 + r') 0 = e0 k r' := by
  funext i
  simp only [phiV', phiV]
  rw [dif_pos (by first | simp | (rw [Fin.val_zero]; omega))]
  rw [mulVec_bvec_eq_col_fun]
  simp only [e0, bvec, Pi.single_apply, Hpk, esI, eI, a0, Fin.val_mk, Fin.ext_iff, Fin.val_zero]
  (try split_ifs) <;> (first | rfl | omega)
end lev
section dl
variable (k r : ℕ)
end dl
section a1
variable (k r' : ℕ)
private lemma phiV_one_add_sc_eq_liftVec (b : Fin (r' + 1)) :
    phiV k (1 + r') (sc r' b) = liftVec k 1 r' (phiV k r' b) := by
  funext i
  have hs : (sc r' b).val = b.val + 1 := rfl
  by_cases hb : b.val < r'
  · have h1 : (sc r' b).val < 1 + r' := by omega
    simp only [phiV]
    rw [dif_pos h1, dif_pos hb]
    simp only [liftVec, bvec, Pi.single_apply, esI, hs, Fin.val_mk, Fin.ext_iff, and_false, false_and, and_true, true_and]
    (try split_ifs) <;> (first | rfl | omega)
  · have h1 : ¬ (sc r' b).val < 1 + r' := by omega
    simp only [phiV]
    rw [dif_neg h1, dif_neg hb]
    simp only [liftVec, epsV, bvec, Pi.smul_apply, Pi.add_apply, Pi.single_apply, wI, Fin.val_mk,
      Fin.ext_iff, and_false, false_and, and_true, true_and, Fin.val_zero, Fin.val_last]
    (try split_ifs) <;> (first | rfl | omega | simp)
private lemma Hpk_succ_mulVec_liftVec (v : Fin (2 * r' + k + 1) → ℂ) :
    Hpk k (1 + r') *ᵥ liftVec k 1 r' v = liftVec k 1 r' (Hpk k r' *ᵥ v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_eq_sum_succ_of_zero_at_edges]
  · by_cases hi : i.val = 0 ∨ i.val = 2 * (1 + r') + k
    · rw [liftVec_apply_of_edge k r' _ i hi]
      apply Finset.sum_eq_zero
      intro b _
      have h0 : Hpk k (1 + r') i ⟨b.val + 1, by omega⟩ = 0 := by
        simp only [Hpk, Fin.val_mk, Fin.ext_iff, and_false, false_and, and_true, true_and]
        (try split_ifs) <;> (first | rfl | omega)
      rw [h0, zero_mul]
    · obtain ⟨a, rfl⟩ : ∃ a : Fin (2 * r' + k + 1),
          (⟨a.val + 1, by omega⟩ : Fin (2 * (1 + r') + k + 1)) = i :=
        ⟨⟨i.val - 1, by omega⟩, Fin.ext (by show i.val - 1 + 1 = i.val; omega)⟩
      simp only [liftVec_apply_succ, Hpk_one_add_apply_succ_succ, Matrix.mulVec, dotProduct]
  · intro j hj
    rw [liftVec_apply_of_edge k r' v j hj, mul_zero]
private lemma phiV'_one_add_sc_eq_liftVec (b : Fin (r' + 1)) :
    phiV' k (1 + r') (sc r' b) = liftVec k 1 r' (phiV' k r' b) := by
  simp only [phiV']
  rw [phiV_one_add_sc_eq_liftVec, Hpk_succ_mulVec_liftVec]
private lemma lev_apply_succ_succ (g : Mat k r') (a b : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g ⟨a.val + 1, by omega⟩ ⟨b.val + 1, by omega⟩ = g a b := by
  first
  | (simp [ιLev]; done)
  | (simp only [ιLev, Fin.val_mk]; rw [dif_pos (by omega), dif_pos (by omega)]; rfl)
private lemma w0_apply_succ_succ (c : ℂ) (a b : Fin (2 * r' + k + 1)) :
    w0 k r' c ⟨a.val + 1, by omega⟩ ⟨b.val + 1, by omega⟩ = if a = b then 1 else 0 := by
  simp only [w0, Fin.val_mk, Fin.ext_iff, and_false, false_and, and_true, true_and]
  (try split_ifs) <;> (first | rfl | omega)
private lemma lev_mulVec_liftVec (g : Mat k r') (u : Fin (2 * r' + k + 1) → ℂ) :
    ιLev k 1 r' g *ᵥ liftVec k 1 r' u = liftVec k 1 r' (g *ᵥ u) := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_eq_sum_succ_of_zero_at_edges]
  · by_cases hi : i.val = 0 ∨ i.val = 2 * (1 + r') + k
    · rw [liftVec_apply_of_edge k r' _ i hi]
      apply Finset.sum_eq_zero
      intro b _
      have h0 : ιLev k 1 r' g i ⟨b.val + 1, by omega⟩ = 0 := by
        simp only [ιLev, Fin.val_mk, Fin.ext_iff, and_false, false_and, and_true, true_and]
        (try split_ifs) <;> (first | rfl | omega)
      rw [h0, zero_mul]
    · obtain ⟨a, rfl⟩ : ∃ a : Fin (2 * r' + k + 1),
          (⟨a.val + 1, by omega⟩ : Fin (2 * (1 + r') + k + 1)) = i :=
        ⟨⟨i.val - 1, by omega⟩, Fin.ext (by show i.val - 1 + 1 = i.val; omega)⟩
      simp only [liftVec_apply_succ, lev_apply_succ_succ, Matrix.mulVec, dotProduct]
  · intro j hj
    rw [liftVec_apply_of_edge k r' u j hj, mul_zero]
private lemma w0_mulVec_liftVec (c : ℂ) (u : Fin (2 * r' + k + 1) → ℂ) :
    w0 k r' c *ᵥ liftVec k 1 r' u = liftVec k 1 r' u := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_eq_sum_succ_of_zero_at_edges]
  · by_cases hi : i.val = 0 ∨ i.val = 2 * (1 + r') + k
    · rw [liftVec_apply_of_edge k r' _ i hi]
      apply Finset.sum_eq_zero
      intro b _
      have h0 : w0 k r' c i ⟨b.val + 1, by omega⟩ = 0 := by
        have hb := b.isLt
        have hil := i.isLt
        simp only [w0]
        split_ifs with h1 h2 h3 <;>
          first | rfl | (exfalso; (try simp only [Fin.val_mk, Fin.ext_iff, and_false, false_and, and_true, true_and] at *); all_goals omega)
      rw [h0, zero_mul]
    · obtain ⟨a, rfl⟩ : ∃ a : Fin (2 * r' + k + 1),
          (⟨a.val + 1, by omega⟩ : Fin (2 * (1 + r') + k + 1)) = i :=
        ⟨⟨i.val - 1, by omega⟩, Fin.ext (by show i.val - 1 + 1 = i.val; omega)⟩
      simp only [liftVec_apply_succ, w0_apply_succ_succ]
      simp
  · intro j hj
    rw [liftVec_apply_of_edge k r' u j hj, mul_zero]
private lemma w0_mul_lev_mulVec_liftVec (c : ℂ) (g : Mat k r') (u : Fin (2 * r' + k + 1) → ℂ) :
    (w0 k r' c * ιLev k 1 r' g) *ᵥ liftVec k 1 r' u = liftVec k 1 r' (g *ᵥ u) := by
  rw [← Matrix.mulVec_mulVec, lev_mulVec_liftVec, w0_mulVec_liftVec]
private lemma w0_mul_lev_mulVec_e0_eq_smul_es0 (c : ℂ) (g : Mat k r') :
    (w0 k r' c * ιLev k 1 r' g) *ᵥ e0 k r' = c • es0 k r' := by
  have h1 : ιLev k 1 r' g *ᵥ e0 k r' = e0 k r' := by
    funext i
    simp only [e0]
    rw [mulVec_bvec_eq_col_fun]
    simp only [ιLev, bvec, Pi.single_apply]
    by_cases hp : 1 ≤ i.val ∧ i.val < 2 * r' + k + 1 + 1
    · have hq : ¬ (1 ≤ (eI k (1 + r') (a0 r')).val ∧
          (eI k (1 + r') (a0 r')).val < 2 * r' + k + 1 + 1) := by
        simp [eI, a0]
      rw [dif_pos hp, dif_neg hq, if_neg]
      intro hh
      rw [hh] at hp
      simp [eI, a0] at hp
    · rw [dif_neg hp]
  have h2 : w0 k r' c *ᵥ e0 k r' = c • es0 k r' := by
    funext i
    simp only [e0, es0]
    rw [mulVec_bvec_eq_col_fun]
    simp only [w0, bvec, Pi.smul_apply, Pi.single_apply, esI, eI, a0, Fin.val_mk, Fin.ext_iff, and_false, false_and, and_true, true_and,
      smul_eq_mul]
    (try split_ifs) <;> (first | omega | simp)
  rw [← Matrix.mulVec_mulVec, h1, h2]
private lemma herm_smul_left_tail_integrals {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (c : ℂ) (v w : Fin m → ℂ) :
    herm H (c • v) w = c * herm H v w := by
  simp [herm, Matrix.mulVec_smul, dotProduct_smul]
end a1
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

set_option autoImplicit false
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution (c : ℂ) (g : Mat k r') (l : Fin (1 + r' + 1)) :
    Dl k (1 + r') l (w0 k r' c * ιLev k 1 r' g) =
      c * (Matrix.of fun a b : Fin l.val =>
        herm (Hpk k r') (g *ᵥ phiV' k r' ⟨b.val, by omega⟩) (phiV' k r' ⟨a.val, by omega⟩)).det := by
  have hc0 : ∀ h : l.val + 1 ≤ 1 + r' + 1, Fin.castLE h (0 : Fin (l.val + 1)) = 0 :=
    fun h => Fin.ext (by simp)
  unfold Dl
  rw [det_eq_mul_minor_of_col_zero_alt]
  · congr 1
    · simp only [Matrix.of_apply, hc0, phiV'_one_add_zero_eq_first_basis_e0_vec, w0_mul_lev_mulVec_e0_eq_smul_es0, herm_smul_left_tail_integrals, herm_last_first_eq_one, mul_one]
    · congr 1
      ext a b
      simp only [Matrix.submatrix_apply, Matrix.of_apply, castLE_succ_eq, phiV'_one_add_sc_eq_liftVec, w0_mul_lev_mulVec_liftVec,
        herm_lift_lift]
  · intro i
    simp only [Matrix.of_apply, hc0, phiV'_one_add_zero_eq_first_basis_e0_vec, w0_mul_lev_mulVec_e0_eq_smul_es0, herm_smul_left_tail_integrals, castLE_succ_eq, phiV'_one_add_sc_eq_liftVec,
      herm_last_lift_eq_zero, mul_zero]
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA

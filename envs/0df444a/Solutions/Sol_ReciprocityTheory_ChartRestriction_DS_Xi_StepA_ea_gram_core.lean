-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ea_gram_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:51:28.215822+00:00
-- url     : https://prove2.me/submissions/556fcc5e-24bd-4288-9aab-0cf6b5c33cbe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LastBasisZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_StarLastDotLast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_star_last_dot_last
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_det_eq_mul_minor_of_col_zero_alt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_dot_lift_lift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_dot_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_last
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_mp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_zero_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_star_last_dot_lift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_star_lift_dot_last
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



set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution {k r' m : ℕ} {κ : Mat k (1 + r')} (hκ : κᴴ * κ = 1) {D : ℝ} (hD : D ≠ 0)
    (W : Fin (m + 1) → Fin (2 * (1 + r') + k + 1) → ℂ) (U : Fin m → Fin (2 * r' + k + 1) → ℂ) (β : Fin m → ℂ)
    (h0 : W 0 = κ *ᵥ ((D : ℂ) • es0 k r'))
    (hs : ∀ i, W i.succ = κ *ᵥ (liftVec k 1 r' (U i) + β i • es0 k r')) :
    Matrix.det (Matrix.of fun a b => star (W a) ⬝ᵥ W b) =
      (D : ℂ) ^ 2 * Matrix.det (Matrix.of fun a b => star (U a) ⬝ᵥ U b) := by
  have hDc : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hD
  have hsD : star (D : ℂ) = D := Complex.conj_ofReal D
  set M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ := Matrix.of fun a b => star (W a) ⬝ᵥ W b with hM
  have e00 : M 0 0 = (D : ℂ) ^ 2 := by
    simp only [hM, of_apply, h0, ea_dot_unit hκ, star_smul, smul_dotProduct, dotProduct_smul, star_last_dot_last,
      smul_eq_mul, hsD]
    ring
  have e0s : ∀ j, M 0 j.succ = (D : ℂ) * β j := by
    intro j
    simp only [hM, of_apply, h0, hs, ea_dot_unit hκ, star_smul, smul_dotProduct, dotProduct_add, dotProduct_smul,
      star_last_dot_lift, star_last_dot_last, smul_eq_mul, hsD]
    ring
  have es : ∀ i, M i.succ 0 = star (β i) * D := by
    intro i
    simp only [hM, of_apply, h0, hs, ea_dot_unit hκ, star_add, star_smul, add_dotProduct, smul_dotProduct,
      dotProduct_smul, star_lift_dot_last, star_last_dot_last, smul_eq_mul]
    ring
  have ess : ∀ i j, M i.succ j.succ = star (U i) ⬝ᵥ U j + star (β i) * β j := by
    intro i j
    simp only [hM, of_apply, hs, ea_dot_unit hκ, star_add, star_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, dot_lift_lift, star_lift_dot_last, star_last_dot_lift, star_last_dot_last, smul_eq_mul]
    ring
  let cc : Fin (m + 1) → ℂ := Fin.cons 0 (fun i => star (β i) / D)
  have hc0 : cc 0 = 0 := by simp [cc]
  have hcs : ∀ i, cc i.succ = star (β i) / D := fun i => by simp [cc]
  have hdet : M.det = (Matrix.of fun i j => M i j - cc i * M 0 j).det := by
    apply det_eq_of_forall_row_eq_smul_add_const cc 0 hc0
    intro i j
    simp only [of_apply, hc0, zero_mul, sub_zero]
    ring
  rw [hdet, det_eq_mul_minor_of_col_zero_alt]
  · have hsub : (Matrix.of fun i j => M i j - cc i * M 0 j).submatrix Fin.succ Fin.succ =
        Matrix.of fun a b => star (U a) ⬝ᵥ U b := by
      ext i j
      simp only [submatrix_apply, of_apply, ess, hcs, e0s]
      field_simp
      ring
    rw [hsub]
    simp only [of_apply, hc0, zero_mul, sub_zero, e00]
  · intro i
    simp only [of_apply, hcs, es, e00]
    field_simp
    ring
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA

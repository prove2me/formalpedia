-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.psiM_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:14:17.399563+00:00
-- url     : https://prove2.me/submissions/f4071c9c-b8c4-42e6-bfc7-57fe5ed85e01

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousConjProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ToMKMulInv
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_toMK_mul__88ef2175972f
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_op_mul__7e3bdcacc26a
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_op_one__4c551cc26830
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_toMK_mul_inv__47a4d626f289
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_psiM_kexp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_inP_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_polar_exists
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_psM_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (T : KType ε Λ) (μ : Fin n → ℤ) (k₁ k₂ : KG ε) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    PsiM T μ (toMK k₁ * g * toMK k₂) = T.op k₁ * PsiM T μ g * T.op k₂ := by
  obtain ⟨k, X, hX, rfl⟩ := polar_exists hg
  obtain ⟨hX', hexp⟩ := inP_conj k₂⁻¹ hX
  rw [inv_inv] at hX' hexp
  have hc := psM_conj T μ k₂⁻¹ (NormedSpace.exp X)
  rw [inv_inv] at hc
  have hg' : toMK k₁ * (toMK k * NormedSpace.exp X) * toMK k₂ =
      toMK (k₁ * k * k₂) * NormedSpace.exp (toMK k₂⁻¹ * X * toMK k₂) := by
    rw [hexp, toMK_mul', toMK_mul']
    simp only [_root_.mul_assoc]
    rw [← _root_.mul_assoc (toMK k₂) (toMK k₂⁻¹), toMK_mul_inv', _root_.one_mul]
  rw [hg', psiM_kexp T μ _ hX', psiM_kexp T μ k hX, hexp, hc, op_mul', op_mul']
  simp only [_root_.mul_assoc]
  rw [← _root_.mul_assoc (T.op k₂) (T.op k₂⁻¹), ← op_mul', mul_inv_cancel, op_one', _root_.one_mul]
end ReciprocityTheory.ChartRestriction.DS.S7

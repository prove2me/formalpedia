-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_sep_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:37:40.515065+00:00
-- url     : https://prove2.me/submissions/19ecfee6-bba7-4ed4-9593-8ce4a9d5ba73

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_mul_inv
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_inv_entry__eb51cf5bfe54

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal
noncomputable section
variable {p q : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
theorem _root_.solution {g h : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hg : IsUpq g) {R c : ℝ}
    (hR : 0 < R) (hc0 : 0 < c) (hgR : ∀ i j, ‖g i j‖ ≤ R) {i j : Fin p ⊕ Fin q}
    (hc : c ≤ ‖(h * g⁻¹) i j - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖) :
    ∃ l, c / (((p + q : ℕ) : ℝ) + 1) / R ≤ ‖h i l - g i l‖ := by
  by_contra hcon
  push_neg at hcon
  have hN : (0 : ℝ) < ((p + q : ℕ) : ℝ) + 1 := by positivity
  have hgi : ∀ l, ‖g⁻¹ l j‖ ≤ R := fun l => by rw [sumBd_inv_entry' hg]; exact hgR j l
  have e : (h * g⁻¹) i j - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j = ((h - g) * g⁻¹) i j := by
    rw [Matrix.sub_mul, sumBd_mul_inv hg, Matrix.sub_apply]
  rw [e, Matrix.mul_apply] at hc
  have hle : ‖∑ l, (h - g) i l * g⁻¹ l j‖ ≤ ∑ _l : Fin p ⊕ Fin q, c / (((p + q : ℕ) : ℝ) + 1) / R * R := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [norm_mul, Matrix.sub_apply]
    exact mul_le_mul (hcon l).le (hgi l) (norm_nonneg _) (by positivity)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul,
    div_mul_cancel₀ _ hR.ne'] at hle
  have h3 : ((p + q : ℕ) : ℝ) * (c / (((p + q : ℕ) : ℝ) + 1)) < c := by
    rw [mul_div_assoc', div_lt_iff₀ hN]
    nlinarith
  push_cast at hle h3
  linarith
end ReciprocityTheory.ChartRestriction.G.AR.Up

-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_inv_entry__eb51cf5bfe54
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:51:44.458959+00:00
-- url     : https://prove2.me/submissions/8b004a51-0b57-4843-b1eb-fc64891f7ab5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBdJf_eq_diag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_inv_eq

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
theorem _root_.solution {g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq g)
    (i j : Fin p ⊕ Fin q) : ‖g⁻¹ i j‖ = ‖g j i‖ := by
  rw [sumBd_inv_eq h, sumBdJf_eq_diag]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  rcases i with i | i <;> rcases j with j | j <;> simp
end ReciprocityTheory.ChartRestriction.G.AR.Up

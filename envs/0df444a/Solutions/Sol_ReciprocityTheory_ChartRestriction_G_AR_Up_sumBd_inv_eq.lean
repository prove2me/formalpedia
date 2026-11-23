-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:35.673807+00:00
-- url     : https://prove2.me/submissions/4b64dc8a-6eee-4d1b-9d26-bbfb5ddfd371

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBdJf_eq_diag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal
noncomputable section
variable {p q : ℕ}
private theorem Jf_mul_self_eq_one : Jf p q * Jf p q = 1 := by
  rw [sumBdJf_eq_diag, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rcases i with i | i <;> simp
private theorem inv_eq_lemma_2 {g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq g) :
    g⁻¹ = Jf p q * gᴴ * Jf p q := by
  have hg : gᴴ * Jf p q * g = Jf p q := h
  apply Matrix.inv_eq_left_inv
  calc Jf p q * gᴴ * Jf p q * g = Jf p q * (gᴴ * Jf p q * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, Jf_mul_self_eq_one]
end
end ReciprocityTheory.ChartRestriction.G.AR.Up
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal
noncomputable section
variable {p q : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
theorem _root_.solution {g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq g) :
    g⁻¹ = Jf p q * gᴴ * Jf p q := inv_eq_lemma_2 h
end ReciprocityTheory.ChartRestriction.G.AR.Up

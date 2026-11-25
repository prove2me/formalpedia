-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_inv_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:37:26.067063+00:00
-- url     : https://prove2.me/submissions/e20f42e6-c9a9-4a27-b296-9fcc6938a22e

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
theorem _root_.solution {g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq g)
    (i j : Fin p ⊕ Fin q) : ‖g⁻¹ i j - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖ =
      ‖g j i - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) j i‖ := by
  have hs : ∀ z : ℂ, ‖(starRingEnd ℂ) z - 1‖ = ‖z - 1‖ := fun z => by
    have h0 := Complex.norm_conj (z - 1)
    rwa [map_sub, map_one] at h0
  rw [inv_eq_lemma_2 h, sumBdJf_eq_diag]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.one_apply]
  rcases i with i | i <;> rcases j with j | j
  · by_cases hij : i = j
    · subst hij; simp [hs]
    · simp [hij, Ne.symm hij]
  · simp
  · simp
  · by_cases hij : i = j
    · subst hij; simp [hs]
    · simp [hij, Ne.symm hij]
end ReciprocityTheory.ChartRestriction.G.AR.Up

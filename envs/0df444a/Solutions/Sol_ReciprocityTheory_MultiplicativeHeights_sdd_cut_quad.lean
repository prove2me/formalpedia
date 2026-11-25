-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sdd_cut_quad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:30:02.51865+00:00
-- url     : https://prove2.me/submissions/833f5f08-4b3b-4bc4-be7d-75af4d1e1c19

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_quad_conj
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_diag_quad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
open scoped ComplexOrder MatrixOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {r k : ℕ} (d : Fin r → ℝ) (hd : ∀ l, 0 ≤ d l) (e : ℕ)
    (E B1 : Matrix (Fin r) (Fin k) ℂ) (hB1 : ∀ l j, B1 l j = if e ≤ (l : ℕ) then E l j else 0)
    (v : Fin k → ℂ) :
    (star v ⬝ᵥ ((B1ᴴ * diagonal (fun l => (d l : ℂ)) * B1) *ᵥ v)).re ≤
      (star v ⬝ᵥ ((Eᴴ * diagonal (fun l => (d l : ℂ)) * E) *ᵥ v)).re := by
  rw [sdd_quad_conj, sdd_quad_conj, sdd_diag_quad, sdd_diag_quad]
  refine Finset.sum_le_sum fun l _ => ?_
  have hrow : (B1 *ᵥ v) l = if e ≤ (l : ℕ) then (E *ᵥ v) l else 0 := by
    by_cases hc : e ≤ (l : ℕ) <;> simp [Matrix.mulVec, dotProduct, hB1, hc]
  rw [hrow]
  split_ifs
  · exact le_rfl
  · rw [norm_zero]
    nlinarith [hd l, sq_nonneg ‖(E *ᵥ v) l‖]
end ReciprocityTheory.MultiplicativeHeights

-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sdd_det_abs_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:41:31.811228+00:00
-- url     : https://prove2.me/submissions/81c9266d-4833-45b2-856e-ff4842fc909e

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_star_self_eig
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_quad_eig

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
theorem _root_.solution {n : ℕ} {D : Matrix (Fin n) (Fin n) ℂ} (hD : D.IsHermitian)
    (h : ∀ w : Fin n → ℂ, ‖star w ⬝ᵥ (D *ᵥ w)‖ ≤ (star w ⬝ᵥ w).re) : ‖D.det‖ ≤ 1 := by
  rw [hD.det_eq_prod_eigenvalues, norm_prod]
  apply Finset.prod_le_one (fun i _ => norm_nonneg _)
  intro i _
  have hi := h (hD.eigenvectorBasis i)
  rwa [sdd_quad_eig hD i, sdd_star_self_eig hD i, Complex.one_re] at hi
end ReciprocityTheory.MultiplicativeHeights

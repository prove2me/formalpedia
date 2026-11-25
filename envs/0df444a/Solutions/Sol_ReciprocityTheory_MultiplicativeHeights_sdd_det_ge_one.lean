-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sdd_det_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:14:33.487906+00:00
-- url     : https://prove2.me/submissions/ac770180-4933-459b-b6b3-d6e9f0dde882

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
    (h : ∀ w : Fin n → ℂ, (star w ⬝ᵥ w).re ≤ (star w ⬝ᵥ (D *ᵥ w)).re) :
    D.det = ((D.det.re : ℝ) : ℂ) ∧ 1 ≤ D.det.re := by
  have hev : ∀ i, 1 ≤ hD.eigenvalues i := by
    intro i
    have hi := h (hD.eigenvectorBasis i)
    rwa [sdd_quad_eig hD i, sdd_star_self_eig hD i, Complex.one_re, Complex.ofReal_re] at hi
  have hdet : D.det = ((∏ i, hD.eigenvalues i : ℝ) : ℂ) := by
    rw [hD.det_eq_prod_eigenvalues, Complex.ofReal_prod]
    rfl
  rw [hdet, Complex.ofReal_re]
  refine ⟨rfl, ?_⟩
  calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => hev i)
end ReciprocityTheory.MultiplicativeHeights

-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sdd_diag_quad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:14:35.801987+00:00
-- url     : https://prove2.me/submissions/dff75bdd-05a0-4a13-a270-457afd279e0b

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDA

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
theorem _root_.solution {r : ℕ} (d : Fin r → ℝ) (x : Fin r → ℂ) :
    (star x ⬝ᵥ (diagonal (fun l => (d l : ℂ)) *ᵥ x)).re = ∑ l, d l * ‖x l‖ ^ 2 := by
  have e : star x ⬝ᵥ (diagonal (fun l => (d l : ℂ)) *ᵥ x) = ∑ l, ((d l * ‖x l‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.star_def, ← mul_assoc, mul_comm ((starRingEnd ℂ) (x l)), mul_assoc, Complex.conj_mul']
    push_cast
    ring
  rw [e, ← Complex.ofReal_sum, Complex.ofReal_re]
end ReciprocityTheory.MultiplicativeHeights

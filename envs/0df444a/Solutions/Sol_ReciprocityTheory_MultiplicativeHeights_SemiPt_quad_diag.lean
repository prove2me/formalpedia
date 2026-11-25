-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.quad_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:29:25.625805+00:00
-- url     : https://prove2.me/submissions/f06804e4-07af-49c2-96bf-ebd4a9615571

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegI
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {r : ℕ} (d w : Fin r → ℂ) :
    star w ⬝ᵥ (diagonal d *ᵥ w) = ∑ a, d a * ((‖w a‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.ofReal_pow, ← Complex.conj_mul', Complex.star_def]
  ring
end ReciprocityTheory.MultiplicativeHeights.SemiPt

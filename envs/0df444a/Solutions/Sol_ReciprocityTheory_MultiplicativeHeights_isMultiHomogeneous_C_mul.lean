-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.isMultiHomogeneous_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:24:10.521828+00:00
-- url     : https://prove2.me/submissions/b56a1476-7ba0-4e3e-9ce8-ddc6c0e916cb

import Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous

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
open MeasureTheory MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {B n : ℕ} {a : Fin B → ℕ} {g : MvPolynomial (Fin B × Fin n) ℂ}
    (hg : IsMultiHomogeneous a g) (c : ℂ) : IsMultiHomogeneous a (C c * g) := by
  intro s hs
  rw [← MvPolynomial.smul_eq_C_mul] at hs
  exact hg s (MvPolynomial.support_smul hs)
end ReciprocityTheory.MultiplicativeHeights

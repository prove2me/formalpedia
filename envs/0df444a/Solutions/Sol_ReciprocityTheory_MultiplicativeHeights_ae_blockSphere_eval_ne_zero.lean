-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.ae_blockSphere_eval_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:53:49.204727+00:00
-- url     : https://prove2.me/submissions/0da2dbb8-cada-4524-a0dd-40922a8789dd

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ae_toSphere
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_blockSphereMeasure_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (B n : ℕ) (a : Fin B → ℕ) (F : MvPolynomial (Fin B × Fin n) ℂ)
    (hF0 : F ≠ 0) (hF : IsMultiHomogeneous a F) :
    ∀ᵐ z ∂(blockSphereProb B n), MvPolynomial.eval (blockPoint z) F ≠ 0 := by
  rw [blockSphereMeasure_eq]
  exact Measure.ae_smul_measure (ae_toSphere B n a F hF0 hF) _
end ReciprocityTheory.MultiplicativeHeights

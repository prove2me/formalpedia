-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.measurable_eval_blockCoords
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:20.002057+00:00
-- url     : https://prove2.me/submissions/71b93856-7c8f-4f3c-a922-6e2e71868eb4

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
theorem _root_.solution {B n : ℕ} (g : MvPolynomial (Fin B × Fin n) ℂ) :
    Measurable fun z : BlockSphere B n => eval (blockPoint z) g := by
  have hc : Continuous fun z : BlockSphere B n => blockPoint z :=
    continuous_pi fun p => (continuous_apply p.2).comp ((PiLp.continuous_ofLp 2 _).comp
      (continuous_subtype_val.comp (continuous_apply p.1)))
  exact ((MvPolynomial.continuous_eval g).comp hc).measurable
end ReciprocityTheory.MultiplicativeHeights

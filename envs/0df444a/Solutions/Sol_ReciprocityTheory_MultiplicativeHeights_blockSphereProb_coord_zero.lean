-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.blockSphereProb_coord_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:31:08.26737+00:00
-- url     : https://prove2.me/submissions/ca7173e0-6b41-4740-ae0b-9155e76a4a17

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sphereProb_coord_zero

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
open MeasureTheory Metric
open scoped Pointwise
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {B n : ℕ} :
    blockSphereProb B n {z | ∃ p : Fin B × Fin n, blockPoint z p = 0} = 0 := by
  rw [Set.ofPred_exists]
  refine measure_iUnion_null fun p => ?_
  show (Measure.pi fun _ : Fin B => sphereProb n)
    (Function.eval p.1 ⁻¹' {w : UnitSphereC n | spherePoint w p.2 = 0}) = 0
  exact Measure.pi_eval_preimage_null _ (sphereProb_coord_zero p.2)
end ReciprocityTheory.MultiplicativeHeights

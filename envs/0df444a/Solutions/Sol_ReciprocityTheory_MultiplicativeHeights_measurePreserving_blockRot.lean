-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.measurePreserving_blockRot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:02:11.41362+00:00
-- url     : https://prove2.me/submissions/be94548e-44c9-4497-a584-d75bb5317ae9

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_measurePreserving_sphereRot

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
theorem _root_.solution {B n : ℕ} (θ : Fin B × Fin n → ℝ) :
    MeasurePreserving (blockRot θ) (blockSphereProb B n) (blockSphereProb B n) := by
  have h : ∀ b : Fin B, MeasurePreserving
      (sphereRot (fun j => Circle.exp (2 * Real.pi * θ (b, j))))
      (sphereProb n) (sphereProb n) := fun b => measurePreserving_sphereRot _
  show MeasurePreserving (fun (z : BlockSphere B n) (b : Fin B) =>
      sphereRot (fun j => Circle.exp (2 * Real.pi * θ (b, j))) (z b))
    (Measure.pi fun _ => sphereProb n) (Measure.pi fun _ => sphereProb n)
  exact measurePreserving_pi (hf := h)
end ReciprocityTheory.MultiplicativeHeights

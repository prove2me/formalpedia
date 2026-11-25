-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.rotLIE_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:14:39.27294+00:00
-- url     : https://prove2.me/submissions/c8e5f865-f0c1-4fea-961d-76163aeb2e1d

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusC

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
theorem _root_.solution {n : ℕ} (u : Fin n → Circle) (x : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    (rotLIE u x).ofLp j = (u j : ℂ) * x.ofLp j := by
  rfl
end ReciprocityTheory.MultiplicativeHeights

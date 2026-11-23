-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.coe_rotS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:59.321795+00:00
-- url     : https://prove2.me/submissions/fadad9e4-137f-4042-b834-337224d1c94e

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_MeasurePreservingSphereMap

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
theorem _root_.solution {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) (θ : ℝ)
    (z : UnitSphereC n) :
    (rotS hu θ z : EuclideanSpace ℂ (Fin n)) =
      inner ℂ u (z : EuclideanSpace ℂ (Fin n)) • u +
        circleMap 0 1 θ • ((z : EuclideanSpace ℂ (Fin n)) - inner ℂ u (z : EuclideanSpace ℂ (Fin n)) • u) :=
  rotCL_apply u _ _
end ReciprocityTheory.MultiplicativeHeights

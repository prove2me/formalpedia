-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.integral_sphMonomMu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:01:46.016336+00:00
-- url     : https://prove2.me/submissions/c462ad60-4d16-4704-8fe8-22914b46c72b

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_GaussSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomStA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Metric Set
variable (N : ℕ)
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (g : EuclideanSpace ℂ (Fin N) → ℂ) :
    ∫ x, g x ∂(sphMonomMu N) = ∫ z, g (sphMonomL N z) :=
  (sphMonomL N).toHomeomorph.measurableEmbedding.integral_map g
end ReciprocityTheory.GeometryOfNumbersTheory

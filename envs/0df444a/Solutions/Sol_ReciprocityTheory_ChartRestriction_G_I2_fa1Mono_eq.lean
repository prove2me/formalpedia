-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.fa1Mono_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:35.77984+00:00
-- url     : https://prove2.me/submissions/4a280b18-0a1f-49f7-8398-ebe96dadf993

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {g : ℕ} (α : Fin g →₀ ℕ) (z : EuclideanSpace ℂ (Fin g)) :
    monomialOfMultiindex α z = ∏ i, z i ^ α i := by
  unfold monomialOfMultiindex
  exact Finset.prod_subset (Finset.subset_univ _) fun i _ hi => by
    rw [Finsupp.notMem_support_iff.mp hi, pow_zero]
end ReciprocityTheory.ChartRestriction.G.I2

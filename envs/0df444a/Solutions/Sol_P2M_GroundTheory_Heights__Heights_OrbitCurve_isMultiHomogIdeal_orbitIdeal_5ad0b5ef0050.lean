-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitCurve_isMultiHomogIdeal_orbitIdeal_5ad0b5ef0050
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:58:07.629706+00:00
-- url     : https://prove2.me/submissions/139ead77-2326-4153-947c-ac036a004539

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCurve
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_weightedHomogeneousComponent_mem_orbitIdeal_da39853aed85

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G Algebra
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitCurve
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.OrbitCurve
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ)) :
    Geo.IsMultiHomogIdeal (ι := blockIdx n) (orbitIdeal x) := by
  classical
  refine ⟨{f | f ∈ orbitIdeal x ∧ ∃ a, Geo.IsMultiHomog (ι := blockIdx n) f a}, fun f hf ↦ hf.2,
    le_antisymm (fun f hf ↦ ?_) (Ideal.span_le.mpr fun f hf ↦ hf.1)⟩
  rw [← sum_weightedHomogeneousComponent (w := coordDeg n) f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
  refine Ideal.sum_mem _ fun m _ ↦
    Ideal.subset_span ⟨weightedHomogeneousComponent_mem_orbitIdeal x hf m, m, ?_⟩
  exact (geoMultiHomog_iff _ m).mpr (weightedHomogeneousComponent_isWeightedHomogeneous m f)
end GroundTheory.Heights₂.Heights.OrbitCurve

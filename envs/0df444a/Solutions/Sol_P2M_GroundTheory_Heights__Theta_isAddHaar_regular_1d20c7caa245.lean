-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_isAddHaar_regular_1d20c7caa245
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:13:27.102912+00:00
-- url     : https://prove2.me/submissions/06d193fb-7106-49db-86bd-758d496ca1f6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LocallyCompactField_Countability

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open MeasureTheory Measure Filter Topology Set
open scoped NNReal ENNReal Pointwise
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddHaarMeasure] : μ.Regular := by
  have h : μ = addHaarScalarFactor μ addHaar • addHaar := by
    ext s _
    have hs : s = ⋃ n, s ∩ compactCovering G n := by
      rw [← inter_iUnion, iUnion_compactCovering, inter_univ]
    have hmono : Monotone (fun n => s ∩ compactCovering G n) :=
      fun m n hmn => inter_subset_inter_right _ (compactCovering_subset G hmn)
    rw [hs, hmono.measure_iUnion, hmono.measure_iUnion]
    congr 1
    funext n
    rw [Measure.smul_apply]
    exact measure_isAddInvariant_eq_smul_of_isCompact_closure μ addHaar
      ((isCompact_compactCovering G n).closure_of_subset inter_subset_right)
  rw [h]
  infer_instance
end GroundTheory.Heights₂.Theta

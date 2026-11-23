-- Prove2me | solution 1 for PI.VolStabW.um_eq_smul_of_sigmaCompact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:13:03.378868+00:00
-- url     : https://prove2.me/submissions/4d1805fc-7c89-4f48-951a-d0e7a6a26971

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_Unimod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open MeasureTheory Measure Topology Set Function
open scoped Pointwise ENNReal NNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace PI.VolStabW
theorem _root_.solution [SigmaCompactSpace G] (μ' μ : Measure G) [IsHaarMeasure μ]
    [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] :
    μ' = haarScalarFactor μ' μ • μ := by
  ext s hs
  have hmono : Monotone (fun n => s ∩ compactCovering G n) :=
    fun m n hmn => inter_subset_inter_right _ (compactCovering_subset G hmn)
  have hU : (⋃ n, s ∩ compactCovering G n) = s := by
    rw [← inter_iUnion, iUnion_compactCovering, inter_univ]
  have key : ∀ n, μ' (s ∩ compactCovering G n) =
      haarScalarFactor μ' μ • μ (s ∩ compactCovering G n) := fun n =>
    measure_isMulInvariant_eq_smul_of_isCompact_closure_of_measurableSet μ' μ
      (hs.inter (isCompact_compactCovering G n).isClosed.measurableSet)
      ((isCompact_compactCovering G n).closure_of_subset inter_subset_right)
  rw [← hU, hmono.measure_iUnion, Measure.smul_apply, hmono.measure_iUnion]
  simp only [key, ENNReal.smul_def, smul_eq_mul]
  rw [ENNReal.mul_iSup]
end PI.VolStabW

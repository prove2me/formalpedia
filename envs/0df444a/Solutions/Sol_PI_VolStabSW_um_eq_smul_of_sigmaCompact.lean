-- Prove2me | solution 1 for PI.VolStabSW.um_eq_smul_of_sigmaCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:56:52.83958+00:00
-- url     : https://prove2.me/submissions/e36f3cca-6241-4adb-833b-a753e1ab8900

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_Unimod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open MeasureTheory Measure Topology Set Function
open scoped Pointwise ENNReal NNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace PI.VolStabSW
theorem _root_.solution [SigmaCompactSpace G] (μ' μ : Measure G) [IsHaarMeasure μ]
    [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] :
    μ' = haarScalarFactor μ' μ • μ := by
  refine (Measure.ext_iff_of_iUnion_eq_univ (iUnion_compactCovering G)).2 fun n => ?_
  ext t ht
  rw [Measure.restrict_apply ht, Measure.restrict_apply ht, Measure.smul_apply]
  exact measure_isMulInvariant_eq_smul_of_isCompact_closure μ' μ
    ((isCompact_compactCovering G n).closure_of_subset Set.inter_subset_right)
end PI.VolStabSW

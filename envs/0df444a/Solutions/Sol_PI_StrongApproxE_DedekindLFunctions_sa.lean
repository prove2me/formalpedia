-- Prove2me | solution 1 for PI.StrongApproxE.DedekindLFunctions.sa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:39.257842+00:00
-- url     : https://prove2.me/submissions/ac02f2bb-1400-4898-ab3e-00e44f32fb14

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_StrongApproxE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StrongApproximation_LocSmall
import Definitions.Def_Lemmata_Cancellation_EnnrealVolumeRatioStepCancel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StrongApproximation_DedekindLFunctions
import Theorems.Thm_Bl_VolumeRatioCancellation_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField
open PI PI.StrongApproxE
open PI.StrongApproxE.DedekindLFunctions
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace PI.StrongApproxE.DedekindLFunctions
theorem _root_.solution (T : Finset (HeightOneSpectrum R)) (a c : HeightOneSpectrum R → K) (hc : ∀ p ∈ T, c p ≠ 0) :
    ∃ t : K, (∀ p ∈ T, p.valuation K (t - a p) ≤ p.valuation K (c p)) ∧
      ∀ p, p ∉ T → p.valuation K t ≤ 1 := by
  first | exact Bl.VolumeRatioCancellation.goal1 .. | (apply Bl.VolumeRatioCancellation.goal1 <;> assumption) | (intros; apply Bl.VolumeRatioCancellation.goal1 <;> assumption)
end PI.StrongApproxE.DedekindLFunctions

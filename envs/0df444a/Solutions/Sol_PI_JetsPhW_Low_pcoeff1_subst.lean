-- Prove2me | solution 1 for PI.JetsPhW.Low.pcoeff1_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:26.110689+00:00
-- url     : https://prove2.me/submissions/cae2ca7f-ad99-49d8-940b-f4252012855a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffSubstOfDegreeEqOne
import Theorems.Thm_PI_JetsPhW_Low_coeff_subst_of_degree_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.JetsPhW PI.JetsPhW.Low
variable {K : Type*} [CommRing K]
namespace PI.JetsPhW.Low
theorem _root_.solution {A : PowerSeries K} (hA : PowerSeries.constantCoeff A = 0)
    (f : PowerSeries K) :
    PowerSeries.coeff 1 (PowerSeries.subst A f : PowerSeries K) =
      PowerSeries.coeff 1 f * PowerSeries.coeff 1 A :=
  coeff_subst_of_degree_eq_one (σ := Unit) hA f (Finsupp.degree_single _ _)
end PI.JetsPhW.Low

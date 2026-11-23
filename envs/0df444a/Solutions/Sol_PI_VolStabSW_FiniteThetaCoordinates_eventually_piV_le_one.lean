-- Prove2me | solution 1 for PI.VolStabSW.FiniteThetaCoordinates.eventually_piV_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:54.208569+00:00
-- url     : https://prove2.me/submissions/5b821251-2026-4e5e-8e35-bd59d2775ee1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FinTheta
import Theorems.Thm_PI_VolStabSW_FiniteThetaCoordinates_norm_le_one_iff_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.FiniteThetaCoordinates
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct
variable (F : Type) [Field F] [NumberField F]
namespace PI.VolStabSW.FiniteThetaCoordinates
theorem _root_.solution (α : AF F) : ∀ᶠ v in Filter.cofinite, ‖piV F v α‖ ≤ 1 := by
  filter_upwards [α.2.2] with v hv
  exact (norm_le_one_iff_mem F v _).2 hv
end PI.VolStabSW.FiniteThetaCoordinates

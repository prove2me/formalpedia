-- Prove2me | solution 1 for PI.AmpRootJacW.shear_mp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:53.762901+00:00
-- url     : https://prove2.me/submissions/79598604-f205-45c3-97b1-78becd681587

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriShear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupJacobian_SUpPowEqZero
import Theorems.Thm_PI_AmpRootJacW_hSh_dep
import Theorems.Thm_PI_AmpRootJacW_continuous_hSh
import Theorems.Thm_PI_AmpRootCommon_Tri_measurePreserving_of_card


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open PI PI.AmpRootJacW
variable {n : ℕ}
variable (S : Finset (Fin n × Fin n))
namespace PI.AmpRootJacW
theorem _root_.solution (hS : ∀ q ∈ S, q.1 < q.2) :
    MeasurePreserving (fun v : S → ℂ => fun q => v q + hSh S q v) volume volume := by
  exact PI.AmpRootCommon.Tri.measurePreserving_of_card (Fintype.card S) S rfl (rk S) (fun q v => hSh S q v)
    (fun q => (continuous_hSh S q).measurable) (fun q x y hxy => hSh_dep S hS q x y hxy)
end PI.AmpRootJacW

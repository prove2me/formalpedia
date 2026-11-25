-- Prove2me | solution 1 for PI.FockOneDegW.kernel_highest_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:47:01.001502+00:00
-- url     : https://prove2.me/submissions/d612fc6a-e209-4215-8b69-bd8af5a26ec5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockRaiseLow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedOps
import Theorems.Thm_PI_FockOneDegW_RedOps_hc_comm_of_homog
import Theorems.Thm_gradedOscillatorProperty


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial FockRaiseLowInner
open PI PI.FockOneDegW
open PI.FockOneDegW.RedOps
namespace PI.FockOneDegW
theorem _root_.solution : KHc := by
  intro p q r s a b hab e P
  refine hc_comm_of_homog _ (fun d P hP => ?_) e P
  have hKC : IsKC (Eab a b) := by
    intro x y hxy
    simp only [Eab, Matrix.single_apply]
    split_ifs with h'
    · obtain ⟨rfl, rfl⟩ := h'
      exact absurd hab hxy
    · rfl
  exact (gradedOscillatorProperty p q r s).1 (Eab a b) hKC d P hP
end PI.FockOneDegW

-- Prove2me | solution 1 for PI.FJMP.exists_mem_support
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:22.372054+00:00
-- url     : https://prove2.me/submissions/0c094402-7c49-4601-8292-183ff22469c2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMP
open PI.FJM
variable {σ : Type*}
namespace PI.FJMP
theorem _root_.solution {P : MvPolynomial σ ℂ} (hP : P ≠ 0) : ∃ e, e ∈ P.support := by
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr (fun h => hP (support_eq_empty.mp h))
  exact ⟨e, he⟩
end PI.FJMP

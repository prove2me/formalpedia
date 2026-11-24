-- Prove2me | solution 1 for PI.ScRefExists.TH.cj_cj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:40:13.246264+00:00
-- url     : https://prove2.me/submissions/7a4c5072-c4ce-45f0-83d2-0eacbfee7a31

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaA
import Theorems.Thm_PI_ScRefExists_TH_mem_cj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.TH
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.TH
theorem _root_.solution (P : HeightOneSpectrum (𝓞 I.E)) : cj I (cj I P) = P := by
  ext x
  rw [mem_cj, mem_cj, sg_sg]
end PI.ScRefExists.TH

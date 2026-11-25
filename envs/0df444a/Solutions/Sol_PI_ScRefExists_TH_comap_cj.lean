-- Prove2me | solution 1 for PI.ScRefExists.TH.comap_cj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:33:10.987111+00:00
-- url     : https://prove2.me/submissions/a64be42d-cbc9-4cfd-b1a4-1f66ce7970ee

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaA
import Theorems.Thm_PI_ScRefExists_TH_sg_alg
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
theorem _root_.solution (P : HeightOneSpectrum (𝓞 I.E)) :
    (cj I P).asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = P.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) := by
  ext c
  rw [Ideal.mem_comap, Ideal.mem_comap, mem_cj, sg_alg]
end PI.ScRefExists.TH

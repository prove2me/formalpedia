-- Prove2me | solution 1 for PI.WAU.Cpt.ctsA_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:05:02.911496+00:00
-- url     : https://prove2.me/submissions/f7ac99e2-2b1d-48b1-8a21-0715b406c233

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_MulVecMemLf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_IsCompactCset
import Theorems.Thm_PI_WAU_ctsA_emb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix
open PI.WAU.Cpt
variable (I : AutInst)
namespace PI.WAU.Cpt
theorem _root_.solution (i j : Fin I.n) : CtsA (bs I) (fun p : Co I × Co I => matOf I p.2 i j) :=
  ctsA_emb ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd))
end PI.WAU.Cpt

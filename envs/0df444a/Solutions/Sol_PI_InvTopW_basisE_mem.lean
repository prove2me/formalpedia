-- Prove2me | solution 1 for PI.InvTopW.basisE_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:55:13.630855+00:00
-- url     : https://prove2.me/submissions/97577a73-9fda-4994-b0b1-afff6d5785c4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_EntriesLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LinearIndependentOneBeta
import Theorems.Thm_PI_InvTopW_beta_mem
import Theorems.Thm_PI_InvTopW_basisE_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvTopW
open NumberField IsDedekindDomain Matrix Topology Filter
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge
variable (I : AutInst)
namespace PI.InvTopW
theorem _root_.solution (k : Fin 2) : basisE I k ∈ Formalism.UG.intOE I.E := by
  rw [basisE_apply]
  fin_cases k
  · exact one_mem _
  · exact beta_mem I
end PI.InvTopW

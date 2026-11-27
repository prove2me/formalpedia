-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ClassReducedParamsNonempty_proof_bc2f76b21936
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:11:11.156259+00:00
-- url     : https://prove2.me/submissions/d2edda33-6410-47f9-8661-1a786ac61d3f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassReducedParamsNonemptyPf
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_IsLatticeParam_smul_fdb7c318695f
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_exists_isLatticeParam_fractionalIdeal_75451ce968be

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open UpperHalfPlane ModularGroup Complex NumberField
open scoped Real MatrixGroups nonZeroDivisors
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Theta
namespace ClassReducedParamsNonempty
theorem _root_.solution : ClassReducedParamsNonempty.Statement := by
  intro K _ _ h2 σ hσ A
  refine ClassGroup.induction (K := K) (fun I => ?_) A
  obtain ⟨τ, hτ⟩ := exists_isLatticeParam_fractionalIdeal h2 σ hσ I
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
  exact ⟨g • τ, I, rfl, hg, hτ.smul g⟩
end ClassReducedParamsNonempty
end GroundTheory.Heights₂.Theta

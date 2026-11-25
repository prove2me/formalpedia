-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_E_mem_u_5833aa7027d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:50:34.781743+00:00
-- url     : https://prove2.me/submissions/4f29d4ef-9881-4f1c-a656-86b68cf01e9a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_E_mem_8815a8a2ccae

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Theta.SecondKind
open GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
namespace GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
theorem _root_.solution (F : OrthoFrame) (l : Fin F.dim) (τ : Fin F.f) :
    F.E l τ ∈ indefiniteUnitaryLieAlgebra (F.p τ) (F.q τ) :=
  (Submodule.mem_pi.1 (E_mem F l)) τ (Set.mem_univ _)
end GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination

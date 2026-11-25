-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_CongruenceLift_exists_nsmul_mem_0148272bd536
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:32:34.015856+00:00
-- url     : https://prove2.me/submissions/049027cc-6608-45b1-9898-321b8c1b2171

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_ExistsNsmulMem_exists_nsmul_mem__79c905849635
import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementExtension
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsNsmulMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PCongruenceLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.CongruenceLift
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.CongruenceLift
theorem _root_.solution {E W : Type*} [Field E] [NumberField E] [AddCommGroup W] [Module E W]
    {La : AddSubgroup W} (hLa : IsLattice E La) (w : W) : ∃ d : ℕ, 0 < d ∧ d • w ∈ La :=
  _root_.P2M_UpperTheory_Reformulated_B_ExistsNsmulMem_exists_nsmul_mem__79c905849635 hLa w
end GroundTheory.Heights₂.Heights.FiniteCovolume.CongruenceLift

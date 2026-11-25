-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_ChainSum_deg_sub_top_8f7be36c5b52
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:09:42.711649+00:00
-- url     : https://prove2.me/submissions/1ef60866-a88b-49fc-81d5-0d6b2f83002e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PChainSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_ChainSum_deg_eq_of_linearEquiv_897173931eb1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gramDet_comap_641348eb9df1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField
open GroundTheory.Heights₂.Heights
universe u v
noncomputable section
open GroundTheory.Heights₂.Heights.LatticeLemmas.ChainSum
namespace GroundTheory.Heights₂.Heights.LatticeLemmas.ChainSum
theorem _root_.solution {K : Type u} [Field K] [NumberField K] (M : HermitianBundle.{v} K) :
    (M.sub ⊤).deg = M.deg :=
  deg_eq_of_linearEquiv (M.sub ⊤) M Submodule.topEquiv fun σ _ s ↦
    gramDet_comap M.metric (⊤ : Submodule (𝓞 K) M.carrier).subtype (Submodule.injective_subtype _) σ s
end GroundTheory.Heights₂.Heights.LatticeLemmas.ChainSum

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_ChainSum_deg_sub_comap_84fe70e9ccca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:02:30.029788+00:00
-- url     : https://prove2.me/submissions/ca70ce2f-b482-4207-a175-0fa49e037f25

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
theorem _root_.solution {K : Type u} [Field K] [NumberField K] (M : HermitianBundle.{v} K)
    {F G : Submodule (𝓞 K) M.carrier} (hGF : G ≤ F) :
    ((M.sub F).sub (G.comap F.subtype)).deg = (M.sub G).deg :=
  deg_eq_of_linearEquiv _ _ (Submodule.comapSubtypeEquivOfLe hGF) fun σ _ s ↦ by
    have e1 := gramDet_comap (M.sub F).metric (G.comap F.subtype).subtype
      (Submodule.injective_subtype _) σ s
    have e2 := gramDet_comap M.metric F.subtype (Submodule.injective_subtype _) σ
      fun i ↦ (G.comap F.subtype).subtype (s i)
    have e3 := gramDet_comap M.metric G.subtype (Submodule.injective_subtype _) σ
      fun i ↦ Submodule.comapSubtypeEquivOfLe hGF (s i)
    exact e1.trans (e2.trans e3.symm)
end GroundTheory.Heights₂.Heights.LatticeLemmas.ChainSum

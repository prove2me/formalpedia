-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.det_subtype_comp_associated_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:22:06.915626+00:00
-- url     : https://prove2.me/submissions/3a7e91d5-f90c-468f-aa12-1dd77569b83d

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_Lemmata_GeneralBFactLast_Imports
import Definitions.Def_Lemmata_GeneralBFactTail_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_DetSubtypeCompAssociatedProd
import Theorems.Thm_Bl_general_b_fact_tail_goal1
import Theorems.Thm_P2M_RH_P2M_Bl_general_b_fact________goal1_21b1a474250b_b320b26946e406da


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Module Submodule
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {R M : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι R M) (N : Submodule R M)
    (h : finrank R N = finrank R M) (e : M ≃ₗ[R] N) :
    Associated (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[R] N)))
      (∏ i, smithNormalFormCoeffs b h i) := by
  first | exact Bl.general_b_fact_tail.goal1 .. | (apply Bl.general_b_fact_tail.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_tail.goal1 <;> assumption)
end ReciprocityTheory.MultiplicativeHeights

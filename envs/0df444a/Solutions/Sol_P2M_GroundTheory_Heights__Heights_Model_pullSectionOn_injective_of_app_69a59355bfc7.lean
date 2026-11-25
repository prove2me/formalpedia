-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_injective_of_app_69a59355bfc7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:42:56.358637+00:00
-- url     : https://prove2.me/submissions/6950c770-6322-4aef-9d49-d6a56c2cac83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericPullInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericPullInj
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_injective_of_basis_of_app_430ada2a134c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_modules_eq_of_locally_0ba002512d62
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_res_5fd6dfc3c9f5


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (hPB : PullbackBasis.Statement.{0}) {T Z : Scheme.{0}}
    (g : T ⟶ Z) (M : Z.Modules) (hM : IsVectorBundle M) (V : Z.Opens)
    (hg : ∀ W : Z.Opens, W ≤ V → Function.Injective (g.app W)) :
    Function.Injective (pullSectionOn g M V) := by
  rw [injective_iff_map_eq_zero]
  intro τ hτ
  apply modules_eq_of_locally M τ 0
  intro x hx
  obtain ⟨U, -, hxU, n, t, ht⟩ := hM x
  refine ⟨U ⊓ V, inf_le_right, ⟨hxU, hx⟩, ?_⟩
  rw [map_zero]
  apply pullSectionOn_injective_of_basis_of_app hPB g M (ht.restrict inf_le_left)
    (hg _ inf_le_right)
  rw [pullSectionOn_res g M inf_le_right (homOfLE ((Opens.map g.base).monotone inf_le_right)) τ,
    hτ, map_zero, map_zero]
end GroundTheory.Heights₂.Heights.Model

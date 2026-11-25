-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_injective_of_basis_of_app_430ada2a134c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:06:15.22008+00:00
-- url     : https://prove2.me/submissions/2d171f24-e3a4-45e2-b644-db28990f7873

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericPullInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericPullInj
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_bijective_self_4d7cdc831e38
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_sum_a72fcb193ca9


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
theorem _root_.solution (hPB : PullbackBasis.Statement.{0})
    {T Z : Scheme.{0}} (g : T ⟶ Z) (M : Z.Modules) {W : Z.Opens} {n : ℕ} {t : Fin n → Γ(M, W)}
    (ht : IsBasisOn M W t) (hg : Function.Injective (g.app W)) :
    Function.Injective (pullSectionOn g M W) := by
  have hb := (hPB _ _ g M W n t ht).bijective_self
  rw [injective_iff_map_eq_zero]
  intro τ hτ
  obtain ⟨r, rfl⟩ := ht.bijective_self.2 τ
  have h0 : (fun i => g.app W (r i)) = 0 := by
    apply hb.1
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
    exact (pullSectionOn_sum g M W t r).symm.trans hτ
  have hr : r = 0 := funext fun i => hg (by rw [Pi.zero_apply, map_zero]; exact congrFun h0 i)
  simp [hr]
end GroundTheory.Heights₂.Heights.Model

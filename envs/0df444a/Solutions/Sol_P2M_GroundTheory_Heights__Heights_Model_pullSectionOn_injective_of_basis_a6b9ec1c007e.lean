-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_injective_of_basis_a6b9ec1c007e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:06:03.45328+00:00
-- url     : https://prove2.me/submissions/484d4764-64e5-4e9f-98fa-7120b6970a25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PullbackBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_RatLocalAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
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
variable (hPB : PullbackBasis.Statement.{0}) (hRL : RatLocalAffine.Statement)
  {X : Scheme.{0}} (f : X ⟶ SpecZ) [Flat f] (L : X.Modules)
  {W : X.Opens} (hW : IsAffineOpen W) {n : ℕ} {t : Fin n → Γ(L, W)} (ht : IsBasisOn L W t)
include hPB hRL hW ht
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution :
    Function.Injective (pullSectionOn (baseChangeMap f ℚ) L W) := by
  have hb := (hPB _ _ (baseChangeMap f ℚ) L W n t ht).bijective_self
  have hinj := (hRL X f W hW).1
  rw [injective_iff_map_eq_zero]
  intro τ hτ
  obtain ⟨r, rfl⟩ := ht.bijective_self.2 τ
  have h0 : (fun i => (baseChangeMap f ℚ).app W (r i)) = 0 := by
    apply hb.1
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
    exact (pullSectionOn_sum _ L W t r).symm.trans hτ
  have hr : r = 0 := funext fun i => hinj (by rw [Pi.zero_apply, map_zero]; exact congrFun h0 i)
  simp [hr]
end GroundTheory.Heights₂.Heights.Model

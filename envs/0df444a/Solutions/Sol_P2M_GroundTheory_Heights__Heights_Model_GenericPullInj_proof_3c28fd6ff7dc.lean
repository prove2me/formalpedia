-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_GenericPullInj_proof_3c28fd6ff7dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:03:25.528191+00:00
-- url     : https://prove2.me/submissions/19a1c6a5-8d27-4ec0-89c8-a76a09dfea46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericPullInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericPullInj
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_injective_of_app_69a59355bfc7

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
namespace GenericPullInj
theorem _root_.solution (h₁ : GenericSectionsInj.Statement)
    (h₂ : PullbackBasis.Statement.{0}) : GenericPullInj.Statement := by
  intro X f _ _ a ha G hG
  obtain ⟨m, hm, hinj⟩ := h₁ X f
  refine ⟨m, hm, fun n hn hmn V hV => ?_⟩
  have hk0 : (a : ℤ) * n ≠ 0 := mul_ne_zero (by exact_mod_cast ha.ne') (by exact_mod_cast hn.ne')
  have hk : IsUnit (((a : ℤ) * n : ℤ) : ℚ) := isUnit_intCast_rat _ hk0
  have hle : invOpen f ((a : ℤ) * n) ≤ invOpen f a := invOpen_mul_le_left f a n
  have hcomp : toInvOpen f ℚ ((a : ℤ) * n) hk ≫ X.homOfLE hle =
      toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) :=
    toInvOpen_homOfLE _ _ _ _ hle
  apply pullSectionOn_injective_of_app h₂ _ G hG V
  intro W hW
  have hWr : W ≤ (X.homOfLE hle).opensRange := by
    rw [Scheme.opensRange_homOfLE]
    exact hW.trans hV
  have hiso : IsIso ((X.homOfLE hle).app W) := Scheme.Hom.isIso_app _ W hWr
  have hj : Function.Injective ((X.homOfLE hle).app W) :=
    (ConcreteCategory.bijective_of_isIso ((X.homOfLE hle).app W)).1
  have hq : Function.Injective ((toInvOpen f ℚ ((a : ℤ) * n) hk).app ((X.homOfLE hle) ⁻¹ᵁ W)) :=
    hinj _ hk (Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr hmn) _) _
  rw [← hcomp, Scheme.Hom.comp_app]
  intro x y hxy
  exact hj (hq hxy)
end GenericPullInj
end GroundTheory.Heights₂.Heights.Model

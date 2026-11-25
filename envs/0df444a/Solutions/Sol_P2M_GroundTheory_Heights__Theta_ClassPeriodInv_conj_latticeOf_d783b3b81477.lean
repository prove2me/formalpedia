-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ClassPeriodInv_conj_latticeOf_d783b3b81477
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:42:36.622808+00:00
-- url     : https://prove2.me/submissions/0a9b1dc1-6069-4522-9dba-fa9884c0f31f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaLogPeriodNegConjPf
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassPeriodInvConj

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
open UpperHalfPlane ModularGroup ModularForm Complex NumberField Module
open scoped Real Modular MatrixGroups nonZeroDivisors
open GroundTheory.Heights₂.Theta.ClassPeriodInv
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Theta.ClassPeriodInv
theorem _root_.solution (z : ℂ) :
    starRingEnd ℂ '' latticeOf z = latticeOf (-(starRingEnd ℂ z)) := by
  unfold latticeOf
  have h : (starRingEnd ℂ '' ((Submodule.span ℤ ({1, z} : Set ℂ)) : Set ℂ)) =
      ((Submodule.span ℤ ({1, z} : Set ℂ)).map
        ((starRingEnd ℂ).toAddMonoidHom.toIntLinearMap) : Set ℂ) := by
    rw [Submodule.map_coe]
    rfl
  rw [h, Submodule.map_span, Set.image_pair]
  congr 1
  simp only [AddMonoidHom.coe_toIntLinearMap, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
    map_one]
  rw [Submodule.span_insert, Submodule.span_insert, ← Submodule.span_neg ({starRingEnd ℂ z} : Set ℂ),
    Set.neg_singleton]
end GroundTheory.Heights₂.Theta.ClassPeriodInv

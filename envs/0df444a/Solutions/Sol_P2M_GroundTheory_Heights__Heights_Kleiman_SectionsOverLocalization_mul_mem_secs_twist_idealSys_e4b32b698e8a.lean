-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_mul_mem_secs_twist_idealSys_e4b32b698e8a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:17:42.896304+00:00
-- url     : https://prove2.me/submissions/a8929b1e-06d9-44a8-8165-42e7ce091f2d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_MulMemSecsTwistIdealSys

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial Kleiman
noncomputable section
variable {R : Type*} [CommRing R] {Ω : Type*} [Field Ω] [Algebra R Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
theorem _root_.solution (J : Ideal (Poly R N)) {a : R} (ha : C a ∈ J)
    (F : SubSystem R x Ω) {y : Ω} (hy : y ∈ F.secs) :
    algebraMap R Ω a * y ∈ (F.twist (idealSys x J)).secs := by
  simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem] at hy ⊢
  intro I
  rw [SubSystem.twist_sub_eq_mul_of_line]
  refine Submodule.mul_mem_mul (Submodule.subset_span ⟨C a, 1, 0, ha, one_mem _, isHomogeneous_C _ _,
    isHomogeneous_one _ _, by simp⟩) (hy I)
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_exists_unitary_first_c8c74f914855
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:53:21.920856+00:00
-- url     : https://prove2.me/submissions/0cf515b1-16e5-4d6d-963b-3347477b2687

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereProjectionLaw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.SphereProjectionLaw
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.SphereProjectionLaw
theorem _root_.solution {m : ℕ} (p : Fin (m + 1) → ℂ) (hp : ∑ j, ‖p j‖ ^ 2 = 1) :
    ∃ U : (Fin (m + 1) → ℂ) →ₗ[ℂ] (Fin (m + 1) → ℂ),
      (∀ v, ∑ j, ‖U v j‖ ^ 2 = ∑ j, ‖v j‖ ^ 2) ∧ ∀ v, U v 0 = coordAlong p v := by
  let p' : EuclideanSpace ℂ (Fin (m + 1)) := WithLp.toLp 2 p
  have hp' : ‖p'‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [p', hp]
  have hon : Orthonormal ℂ (({0} : Set (Fin (m + 1))).domRestrict fun _ ↦ p') := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [Subsingleton.elim i j, if_pos rfl,
      show (({0} : Set (Fin (m + 1))).domRestrict fun _ ↦ p') j = p' from rfl,
      inner_self_eq_norm_sq_to_K, hp']
    simp
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hb0 : b 0 = p' := hb 0 (Set.mem_singleton 0)
  let Ulin : (Fin (m + 1) → ℂ) ≃ₗ[ℂ] (Fin (m + 1) → ℂ) :=
    (WithLp.linearEquiv 2 ℂ (Fin (m + 1) → ℂ)).symm ≪≫ₗ b.repr.toLinearEquiv ≪≫ₗ
      WithLp.linearEquiv 2 ℂ (Fin (m + 1) → ℂ)
  have hUapp : ∀ v, Ulin v = (b.repr (WithLp.toLp 2 v)).ofLp := fun v ↦ rfl
  refine ⟨Ulin.toLinearMap, fun v ↦ ?_, fun v ↦ ?_⟩
  · have h := b.repr.norm_map (WithLp.toLp 2 v)
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq] at h
    have h2 := congrArg (· ^ 2) h
    simp only [Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)] at h2
    simpa [hUapp] using h2
  · rw [LinearEquiv.coe_coe, hUapp, OrthonormalBasis.repr_apply_apply, hb0, PiLp.inner_apply]
    simp [p', RCLike.inner_apply, coordAlong]
end GroundTheory.Heights₂.Heights.SphereProjectionLaw

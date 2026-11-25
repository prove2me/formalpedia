-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_sum_norm_sq_sub_ddb4e8b7c1b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:53:24.317021+00:00
-- url     : https://prove2.me/submissions/935a620a-4dac-4f0b-8ec9-eea76bc7a292

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereProjectionLaw
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_ofReal_norm_sq_0f7fc2aa98eb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_ofReal_sum_norm_sq_3d58e7f47ece

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
theorem _root_.solution {p z : Fin n → ℂ} (hp : ∑ j, ‖p j‖ ^ 2 = 1)
    (hz : ∑ j, ‖z j‖ ^ 2 = 1) :
    ∑ j, ‖(z - coordAlong p z • p) j‖ ^ 2 = 1 - ‖coordAlong p z‖ ^ 2 := by
  apply Complex.ofReal_injective
  set a := coordAlong p z with ha
  have hzp : ∑ j, p j * star (z j) = star a := by
    simp [ha, coordAlong, star_sum, mul_comm]
  have hpp : ∑ j, p j * star (p j) = 1 := by rw [← ofReal_sum_norm_sq, hp, Complex.ofReal_one]
  have hzz : ∑ j, z j * star (z j) = 1 := by rw [← ofReal_sum_norm_sq, hz, Complex.ofReal_one]
  have key : ∀ j, (z - a • p) j * star ((z - a • p) j) =
      z j * star (z j) - star a * (z j * star (p j)) - a * (p j * star (z j)) +
        a * star a * (p j * star (p j)) := by
    intro j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, star_sub, star_mul']
    ring
  rw [ofReal_sum_norm_sq, Finset.sum_congr rfl fun j _ ↦ key j]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hzp, hpp, hzz, ← coordAlong, ← ha, Complex.ofReal_sub, Complex.ofReal_one,
    ofReal_norm_sq]
  ring
end GroundTheory.Heights₂.Heights.SphereProjectionLaw

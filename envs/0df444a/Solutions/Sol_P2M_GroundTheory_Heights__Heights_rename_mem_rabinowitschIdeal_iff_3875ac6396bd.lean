-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_rename_mem_rabinowitschIdeal_iff_3875ac6396bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:47:56.302443+00:00
-- url     : https://prove2.me/submissions/f26acbb2-3074-4ead-aa19-13dff565d396

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RadicalAwayRabinowitsch
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_pow_sub_one_mem_span_ca487896d56f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_rabinowitschEval_rename_ff6a73805728
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_rabinowitschIdeal_le_ker_add408c5818c

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
open MvPolynomial
noncomputable section
variable {R : Type*} [CommRing R] {ι : Type*}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (K : Ideal (MvPolynomial ι R)) (g f : MvPolynomial ι R) :
    rename some f ∈ rabinowitschIdeal K g ↔ ∃ k : ℕ, g ^ k * f ∈ K := by
  constructor
  · intro hf
    have h0 := rabinowitschIdeal_le_ker K g hf
    rw [RingHom.mem_ker, rabinowitschEval_rename,
      IsLocalization.map_eq_zero_iff (Submonoid.powers (Ideal.Quotient.mk K g))] at h0
    obtain ⟨⟨m, k, rfl⟩, hm⟩ := h0
    refine ⟨k, Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩
    simpa using hm
  · rintro ⟨k, hk⟩
    have e : (rename some f : MvPolynomial (Option ι) R) =
        X none ^ k * rename some (g ^ k * f) -
          rename some f * ((X none * rename some g) ^ k - 1) := by
      simp only [map_mul, map_pow]; ring
    rw [e]
    refine Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_sup_left ?_))
      (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (pow_sub_one_mem_span g k)))
    exact Ideal.mem_map_of_mem _ hk
end GroundTheory.Heights₂.Heights

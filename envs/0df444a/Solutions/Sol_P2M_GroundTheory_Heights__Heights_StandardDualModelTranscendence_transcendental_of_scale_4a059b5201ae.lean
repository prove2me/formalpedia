-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_transcendental_of_scale_4a059b5201ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:19:36.37519+00:00
-- url     : https://prove2.me/submissions/f806ba25-99ad-4b33-b7af-5788f18c0771

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdModelTransc

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.StandardDualModelTranscendence
variable {L : Type} [Field L]
namespace GroundTheory.Heights₂.Heights.StandardDualModelTranscendence
theorem _root_.solution {R Ω : Type} [CommRing R] [Field Ω] [CharZero Ω] [Algebra R Ω]
    (A : Subalgebra R Ω) {z : Ω} (hz : z ≠ 0)
    (h : ∀ n : ℕ, ∃ σ : Ω →+* Ω, (∀ y ∈ A, σ y = y) ∧ σ z = ((n : Ω) + 1) * z) : Transcendental A z := by
  rintro ⟨p, hp0, hp⟩
  rw [Polynomial.aeval_def] at hp
  have hroot : ∀ n : ℕ, Polynomial.eval₂ (algebraMap A Ω) (((n : Ω) + 1) * z) p = 0 := by
    intro n
    obtain ⟨σ, hfix, hσz⟩ := h n
    have hcomp : σ.comp (algebraMap A Ω) = algebraMap A Ω := RingHom.ext fun y => hfix y y.2
    have h' := Polynomial.hom_eval₂ p (algebraMap A Ω) σ z
    rw [hp, map_zero, hcomp, hσz] at h'
    exact h'.symm
  have hq : p.map (algebraMap A Ω) ≠ 0 := (Polynomial.map_ne_zero_iff fun x y h => Subtype.ext h).mpr hp0
  refine hq (Polynomial.eq_zero_of_infinite_isRoot _ ?_)
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n : Ω) + 1) * z) (fun n m hnm => ?_) fun n => ?_
  · exact Nat.cast_injective (add_right_cancel (mul_right_cancel₀ hz hnm))
  · change Polynomial.IsRoot _ _
    rw [Polynomial.IsRoot, Polynomial.eval_map]
    exact hroot n
end GroundTheory.Heights₂.Heights.StandardDualModelTranscendence

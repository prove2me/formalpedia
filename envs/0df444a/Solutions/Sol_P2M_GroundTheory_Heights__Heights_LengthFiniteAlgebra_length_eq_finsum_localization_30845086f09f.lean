-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_length_eq_finsum_localization_30845086f09f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:03:03.765184+00:00
-- url     : https://prove2.me/submissions/4e531ddf-0141-46ea-98b6-1213761a8b94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PLengthFiniteAlgebra
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_finite_maximalSpectrum_4974b2542461

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
open IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.LengthFiniteAlgebra
variable {O B : Type} [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B]
namespace GroundTheory.Heights₂.Heights.LengthFiniteAlgebra
theorem _root_.solution [IsNoetherianRing O] [Module.Finite O B] :
    Module.length O B =
      ∑ᶠ P : MaximalSpectrum B, Module.length O (Localization.AtPrime P.asIdeal) := by
  have := finite_maximalSpectrum (O := O) (B := B)
  let := Fintype.ofFinite (MaximalSpectrum B)
  rw [finsum_eq_sum_of_fintype, ← Module.length_pi_of_fintype]
  let φ : B →ₗ[O] (∀ P : MaximalSpectrum B, Localization.AtPrime P.asIdeal) :=
    LinearMap.pi fun P => (IsScalarTower.toAlgHom O B (Localization.AtPrime P.asIdeal)).toLinearMap
  have hφ : Function.Injective φ := by
    intro x y h
    apply MaximalSpectrum.toPiLocalization_injective B
    funext P
    exact congrFun h P
  by_cases h : Module.length O B = ⊤
  · rw [h]
    exact (top_le_iff.mp (h ▸ Module.length_le_of_injective φ hφ)).symm
  · have hfl : IsFiniteLength O B := Module.length_ne_top_iff.mp h
    rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl
    have : IsArtinianRing B := isArtinian_of_tower O hfl.2
    have hsurj : Function.Surjective φ := by
      intro z
      obtain ⟨x, hx⟩ := PrimeSpectrum.maximalSpectrumToPiLocalization_surjective_of_discreteTopology B z
      exact ⟨x, hx⟩
    exact (LinearEquiv.ofBijective φ ⟨hφ, hsurj⟩).length_eq
end GroundTheory.Heights₂.Heights.LengthFiniteAlgebra

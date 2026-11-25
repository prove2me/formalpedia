-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_finsum_reindex_9a25be9a211b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:39:13.108839+00:00
-- url     : https://prove2.me/submissions/2e2149c3-698b-4662-bfa7-2755ec88da65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PLengthFiniteAlgebra
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_finite_maximalSpectrum_4974b2542461
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_length_localization_quotient_a5622d7b17c9

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
theorem _root_.solution [Module.Finite O B] (θ : B) :
    ∑ᶠ Q : MaximalSpectrum (B ⧸ Ideal.span {θ}), Module.length O (Localization.AtPrime Q.asIdeal) =
      ∑ᶠ P : MaximalSpectrum B, Module.length O (Localization.AtPrime P.asIdeal ⧸
        Ideal.span {algebraMap B (Localization.AtPrime P.asIdeal) θ}) := by
  have := finite_maximalSpectrum (O := O) (B := B)
  have : Module.Finite O (B ⧸ Ideal.span {θ}) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ O _).toLinearMap Ideal.Quotient.mk_surjective
  have := finite_maximalSpectrum (O := O) (B := B ⧸ Ideal.span {θ})
  let := Fintype.ofFinite (MaximalSpectrum B)
  let := Fintype.ofFinite (MaximalSpectrum (B ⧸ Ideal.span {θ}))
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  let ι : MaximalSpectrum (B ⧸ Ideal.span {θ}) → MaximalSpectrum B := fun Q =>
    ⟨Q.asIdeal.comap (Ideal.Quotient.mk _), by
      have := Q.isMaximal; exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective⟩
  refine Fintype.sum_of_injective ι ?_ _ _ ?_ ?_
  · intro Q₁ Q₂ h
    exact MaximalSpectrum.ext (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
      (congrArg MaximalSpectrum.asIdeal h))
  · intro P hP
    have hθ : θ ∉ P.asIdeal := by
      intro hθ
      apply hP
      have hle : Ideal.span {θ} ≤ P.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hθ
      have := P.isMaximal
      have hmax := Ideal.IsMaximal.map_of_surjective_of_ker_le (m := P.asIdeal)
        (f := Ideal.Quotient.mk (Ideal.span {θ})) Ideal.Quotient.mk_surjective
        (by rwa [Ideal.mk_ker])
      exact ⟨⟨_, hmax⟩, MaximalSpectrum.ext (Ideal.comap_map_mk hle)⟩
    have hu : IsUnit (algebraMap B (Localization.AtPrime P.asIdeal) θ) :=
      IsLocalization.map_units (Localization.AtPrime P.asIdeal) (⟨θ, hθ⟩ : P.asIdeal.primeCompl)
    rw [Ideal.span_singleton_eq_top.mpr hu]
    exact Module.length_eq_zero
  · intro Q
    have := Q.isMaximal
    rw [length_localization_quotient (Ideal.span {θ}) Q.asIdeal, Ideal.map_span, Set.image_singleton]
end GroundTheory.Heights₂.Heights.LengthFiniteAlgebra

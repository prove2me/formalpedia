-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SpecCompDim_proof_172508824a98
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:54:11.125056+00:00
-- url     : https://prove2.me/submissions/b34cb389-1a5a-4024-a3c3-af6f87fa15fc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFibreCompDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PMinimalPrimeHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecCompDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_homogeneousComponent_map_coeffs_93ef5918ee46
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimeHomog_proof_bf27ffa11a53


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
namespace SpecCompDim
theorem _root_.solution (hCone : ConeDimOfChowForm.Statement) (hFib : FibreCompDim.Statement) :
    SpecCompDim.Statement := by
  intro K _ _ n e I f v hI hf W hW
  have : v.asIdeal.IsMaximal := v.isMaximal
  have : I.IsPrime := hI.isPrime
  let k := v.asIdeal.ResidueField
  let φ : MvPolynomial (Fin n) (𝓞 K) →+* MvPolynomial (Fin n) k :=
    MvPolynomial.map (algebraMap (𝓞 K) k)
  let ψ : MvPolynomial (Fin n) (𝓞 K) →+* MvPolynomial (Fin n) K :=
    MvPolynomial.map (algebraMap (𝓞 K) K)
  have hφ : Function.Surjective φ :=
    MvPolynomial.map_surjective _ (Ideal.algebraMap_residueField_surjective _)
  have hker : RingHom.ker φ = Ideal.map C v.asIdeal := by
    rw [MvPolynomial.ker_map, Ideal.ker_algebraMap_residueField]
  obtain ⟨hWmin, hWrel⟩ := hW
  have hWprime : W.IsPrime := hWmin.1.1
  have hkerW : RingHom.ker φ ≤ W := hker ▸ le_sup_right.trans hWmin.1.2

  have hP : (integralModel I).IsPrime := Ideal.comap_isPrime ψ I
  have hPC : (integralModel I).comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) = ⊥ := by
    ext c
    simp only [Ideal.mem_comap, integralModel, Ideal.mem_bot]
    constructor
    · intro h
      by_contra hc
      have hu : IsUnit (ψ (C c)) := by
        rw [show ψ (C c) = C (algebraMap (𝓞 K) K c) from map_C _ _]
        exact (isUnit_iff_ne_zero.mpr
          ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hc)).map C
      exact hI.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
    · rintro rfl
      simp
  have hPloc : (integralModel I).map ψ = I := by
    let _ := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := 𝓞 K) (S := K)
    have := MvPolynomial.isLocalization (σ := Fin n) (nonZeroDivisors (𝓞 K)) K
    exact IsLocalization.map_under ((nonZeroDivisors (𝓞 K)).map (C (σ := Fin n)))
      (MvPolynomial (Fin n) K) I
  have hdim := hFib (𝓞 K) K n (integralModel I) W v hP hPC hWmin
  rw [hPloc, hCone K n (e + 1) I f hI hf] at hdim
  refine ⟨⟨Ideal.map_isPrime_of_surjective hφ hkerW, ?_, ?_⟩, hdim⟩
  ·
    have hmin : reduceMod v W ∈ (reduceMod v (integralModel I)).minimalPrimes := by
      change W.map φ ∈ ((integralModel I).map φ).minimalPrimes
      rw [Ideal.minimalPrimes_map_of_surjective hφ, hker]
      exact ⟨W, hWmin, rfl⟩
    refine MinimalPrimeHomog.proof k n _ _ ?_ hmin
    intro g hg d
    change g ∈ (integralModel I).map φ at hg
    obtain ⟨p, hp, rfl⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).mp hg
    rw [homogeneousComponent_map_coeffs]
    refine Ideal.mem_map_of_mem φ ?_
    change ψ (homogeneousComponent d p) ∈ I
    rw [← homogeneousComponent_map_coeffs]
    exact hI.isHomog _ hp d
  ·
    obtain ⟨j, hj⟩ := hWrel
    refine ⟨j, fun h => hj ?_⟩
    have h' : X j ∈ (W.map φ).comap φ := by
      rw [Ideal.mem_comap, map_X]
      exact h
    rwa [Ideal.comap_map_of_surjective _ hφ, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hkerW] at h'
end SpecCompDim
end GroundTheory.Heights₂.Heights.Vertical

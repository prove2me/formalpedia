-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_localMult_map_equiv_39fad21a977d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:44:36.188725+00:00
-- url     : https://prove2.me/submissions/cfd8ac86-f91d-40dd-a4da-9b6cd554f5db

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_length_self_eq_of_ringEquiv_635abfc27369

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc)
namespace GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B] (Ψ : A ≃+* B) (K W : Ideal A) :
    localMult (K.map (Ψ : A →+* B)) (W.map (Ψ : A →+* B)) = localMult K W := by
  classical
  have hWc : (W.map (Ψ : A →+* B)).comap (Ψ : A →+* B) = W := by
    rw [Ideal.map_comap_of_equiv]
    ext x
    simp [Ideal.mem_comap]
  by_cases hW : W.IsPrime
  · haveI := hW
    haveI hW' : (W.map (Ψ : A →+* B)).IsPrime := Ideal.map_isPrime_of_equiv _
    have H : W.primeCompl.map Ψ.toMonoidHom = (W.map (Ψ : A →+* B)).primeCompl := by
      ext x
      rw [Submonoid.mem_map, Ideal.mem_primeCompl_iff, Ideal.map_comap_of_equiv, Ideal.mem_comap]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [Ideal.mem_primeCompl_iff] at hy
        simpa using hy
      · intro hx
        exact ⟨Ψ.symm x, (Ideal.mem_primeCompl_iff).mpr hx, by simp⟩
    let σ : Localization.AtPrime W ≃+* Localization.AtPrime (W.map (Ψ : A →+* B)) :=
      IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime W)
        (Localization.AtPrime (W.map (Ψ : A →+* B))) Ψ H
    have hIJ : (K.map (Ψ : A →+* B)).map (algebraMap B (Localization.AtPrime (W.map (Ψ : A →+* B)))) =
        (K.map (algebraMap A (Localization.AtPrime W))).map (σ : _ →+* _) := by
      rw [Ideal.map_map, Ideal.map_map]
      congr 1
      ext x
      exact (IsLocalization.ringEquivOfRingEquiv_eq H x).symm
    let τ := Ideal.quotientEquiv _ _ σ hIJ
    have e1 : Module.length (Localization.AtPrime W)
        (Localization.AtPrime W ⧸ K.map (algebraMap A (Localization.AtPrime W))) =
        Module.length (Localization.AtPrime W ⧸ K.map (algebraMap A (Localization.AtPrime W)))
          (Localization.AtPrime W ⧸ K.map (algebraMap A (Localization.AtPrime W))) :=
      Module.length_eq_of_surjective (by exact Ideal.Quotient.mk_surjective)
    have e2 : Module.length (Localization.AtPrime (W.map (Ψ : A →+* B)))
        (Localization.AtPrime (W.map (Ψ : A →+* B)) ⧸ (K.map (Ψ : A →+* B)).map
          (algebraMap B (Localization.AtPrime (W.map (Ψ : A →+* B))))) =
        Module.length (Localization.AtPrime (W.map (Ψ : A →+* B)) ⧸ (K.map (Ψ : A →+* B)).map
            (algebraMap B (Localization.AtPrime (W.map (Ψ : A →+* B)))))
          (Localization.AtPrime (W.map (Ψ : A →+* B)) ⧸ (K.map (Ψ : A →+* B)).map
            (algebraMap B (Localization.AtPrime (W.map (Ψ : A →+* B))))) :=
      Module.length_eq_of_surjective (by exact Ideal.Quotient.mk_surjective)
    unfold localMult
    rw [dif_pos hW', dif_pos hW, e1, e2, length_self_eq_of_ringEquiv τ]
  · have hW' : ¬ (W.map (Ψ : A →+* B)).IsPrime := fun h => hW (hWc ▸ Ideal.comap_isPrime _ _)
    unfold localMult
    rw [dif_neg hW', dif_neg hW]
end GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity

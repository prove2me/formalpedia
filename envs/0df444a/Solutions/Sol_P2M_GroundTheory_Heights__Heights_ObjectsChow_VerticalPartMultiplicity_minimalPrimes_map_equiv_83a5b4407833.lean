-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_minimalPrimes_map_equiv_83a5b4407833
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:55:29.316458+00:00
-- url     : https://prove2.me/submissions/753d4375-d17a-428f-8d1b-8c33b5ef3777

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
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
variable {n : ℕ}
theorem keyAux {A B : Type*} [CommRing A] [CommRing B] (Φ : A ≃+* B) (K P : Ideal A) (hP : P ∈ K.minimalPrimes) :
    P.map (Φ : A →+* B) ∈ (K.map (Φ : A →+* B)).minimalPrimes := by
  have hm : ∀ I : Ideal A, I.map (Φ : A →+* B) = I.comap (Φ.symm : B →+* A) := fun I => Ideal.map_comap_of_equiv Φ
  have hp : P.IsPrime := hP.1.1
  refine ⟨⟨?_, Ideal.map_mono hP.1.2⟩, ?_⟩
  · rw [hm]; exact Ideal.IsPrime.comap _
  · rintro Q ⟨hQ, hKQ⟩ hQP
    have h1 : Q.comap (Φ : A →+* B) ≤ P := by
      intro a ha
      have := hQP ha
      rw [hm, Ideal.mem_comap] at this
      simpa using this
    have h2 : K ≤ Q.comap (Φ : A →+* B) := fun a ha => hKQ (Ideal.mem_map_of_mem _ ha)
    have h3 := hP.2 ⟨Ideal.IsPrime.comap _, h2⟩ h1
    rw [Ideal.map_le_iff_le_comap]; exact h3

theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B] (Φ : A ≃+* B) (K : Ideal A) :
    (K.map (Φ : A →+* B)).minimalPrimes = Ideal.map (Φ : A →+* B) '' K.minimalPrimes := by
  have rt : ∀ I : Ideal B, (I.map (Φ.symm : B →+* A)).map (Φ : A →+* B) = I := by
    intro I
    rw [Ideal.map_map]
    have : (Φ : A →+* B).comp (Φ.symm : B →+* A) = RingHom.id B := by ext; simp
    rw [this, Ideal.map_id]
  have rt' : (K.map (Φ : A →+* B)).map (Φ.symm : B →+* A) = K := by
    rw [Ideal.map_map]
    have : (Φ.symm : B →+* A).comp (Φ : A →+* B) = RingHom.id A := by ext; simp
    rw [this, Ideal.map_id]
  ext Q
  constructor
  · intro hQ
    refine ⟨Q.map (Φ.symm : B →+* A), ?_, rt Q⟩
    have := keyAux Φ.symm (K.map (Φ : A →+* B)) Q hQ
    rwa [rt'] at this
  · rintro ⟨P, hP, rfl⟩
    exact keyAux Φ K P hP




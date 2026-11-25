-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_maximalIdeal_le_map_of_transcendental_c5afbfdca7b0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:43:03.049808+00:00
-- url     : https://prove2.me/submissions/3d9fff11-70b5-4b69-8219-835c9fa0fa39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpOrderLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpLocalChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {D : Type*} [CommRing D] [IsDomain D] [IsLocalRing D]
    (hdim : ringKrullDim D ≤ 1) (C : Subring D) (w : D)
    (hinj : Function.Injective (Polynomial.eval₂RingHom C.subtype w))
    (hsurj : ∀ d : D, ∃ a b : Polynomial C,
      Polynomial.eval₂RingHom C.subtype w b ∉ IsLocalRing.maximalIdeal D ∧
      Polynomial.eval₂RingHom C.subtype w b * d = Polynomial.eval₂RingHom C.subtype w a)
    (c₀ : C) (hc₀ : (c₀ : D) ≠ 0) (hc₀m : (c₀ : D) ∈ IsLocalRing.maximalIdeal D) :
    IsLocalRing.maximalIdeal D ≤
      ((IsLocalRing.maximalIdeal D).comap C.subtype).map C.subtype := by
  set φ := Polynomial.eval₂RingHom C.subtype w with hφ
  set m := IsLocalRing.maximalIdeal D with hm
  set p' : Ideal (Polynomial C) := m.comap φ with hp'
  have : p'.IsPrime := Ideal.comap_isPrime φ m
  let : Algebra (Polynomial C) D := φ.toAlgebra
  have hal : ∀ a, algebraMap (Polynomial C) D a = φ a := fun _ => rfl
  have : IsLocalization.AtPrime D p' := by
    refine (isLocalization_iff _ _).mpr ?_
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨b, hb⟩
      rw [hal]
      exact IsLocalRing.notMem_maximalIdeal.mp hb
    · intro d
      obtain ⟨a, b, hb, h⟩ := hsurj d
      exact ⟨⟨a, ⟨b, hb⟩⟩, by rw [hal, hal, mul_comm]; exact h⟩
    · intro x y h
      rw [hal, hal] at h
      exact ⟨1, by rw [hinj h]⟩
  set n := m.comap C.subtype with hn
  have hN : (n.map (Polynomial.C : C →+* Polynomial C)).IsPrime := Ideal.isPrime_map_C_of_isPrime
  have hNp : n.map (Polynomial.C : C →+* Polynomial C) ≤ p' := by
    rw [Ideal.map_le_iff_le_comap]
    intro c hc
    simp only [Ideal.mem_comap, p', φ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    exact hc
  have hI := IsLocalization.isPrime_of_isPrime_disjoint p'.primeCompl D _ hN (by
    rw [Set.disjoint_left]
    intro a ha haN
    exact ha (hNp haN))
  have hmap : (n.map (Polynomial.C : C →+* Polynomial C)).map (algebraMap (Polynomial C) D) =
      n.map C.subtype := by
    rw [Ideal.map_map]
    congr 1
    ext c
    simp [hal, φ]
  rw [hmap] at hI
  have hne : n.map C.subtype ≠ ⊥ := by
    intro h
    apply hc₀
    have : (c₀ : D) ∈ n.map C.subtype := Ideal.mem_map_of_mem C.subtype (show c₀ ∈ n from hc₀m)
    rwa [h, Ideal.mem_bot] at this
  have : Ring.KrullDimLE 1 D := by
    rw [Ring.krullDimLE_iff]
    exact_mod_cast hdim
  have hmax := Ring.krullDimLE_one_iff_of_noZeroDivisors.mp this _ hne hI
  exact (IsLocalRing.eq_maximalIdeal hmax).ge
end GroundTheory.Heights₂.Heights.NumbersDVR

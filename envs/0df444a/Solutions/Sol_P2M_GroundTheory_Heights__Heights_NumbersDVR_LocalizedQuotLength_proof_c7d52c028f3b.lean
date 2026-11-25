-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_LocalizedQuotLength_proof_c7d52c028f3b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:34:27.85349+00:00
-- url     : https://prove2.me/submissions/572944ff-7488-47e2-8975-83a436c8b1a6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpOrderLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PLocalizedQuotLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
universe u
private theorem length_self_eq_of_ringEquiv' {S T : Type*} [CommRing S] [CommRing T] (e : S ≃+* T) :
    Module.length S S = Module.length T T := by
  rw [Module.length_eq_coheight, Module.length_eq_coheight]
  have := Ideal.coheight_comap_of_surjective (e : S →+* T) e.surjective ⊥
  have hb : Ideal.comap (e : S →+* T) ⊥ = ⊥ := Ideal.comap_bot_of_injective _ e.injective
  rw [hb] at this
  exact this
private theorem length_localizedModule_quot' {R : Type*} [CommRing R] (J W : Ideal R) [W.IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) =
      Module.length (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
        (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) := by
  let S := Localization.AtPrime W
  have hJ : (J : Submodule R R).localized' S W.primeCompl (Algebra.linearMap R S) =
      J.map (algebraMap R S) := by
    rw [Submodule.localized'_eq_span, Ideal.map]
    rfl
  let e := (IsLocalizedModule.linearEquiv W.primeCompl
    ((J : Submodule R R).toLocalizedQuotient' S W.primeCompl (Algebra.linearMap R S))
    (LocalizedModule.mkLinearMap W.primeCompl (R ⧸ J))).extendScalarsOfIsLocalization W.primeCompl S
  rw [← e.length_eq, (Submodule.quotEquivOfEq _ _ hJ).length_eq]
  exact Module.length_eq_of_surjective Ideal.Quotient.mk_surjective
end GroundTheory.Heights₂.Heights.NumbersDVR
end

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace LocalizedQuotLength
theorem _root_.solution : LocalizedQuotLength.Statement.{u} := by
  intro S _ P W₀ _ z
  set W := W₀.comap (Ideal.Quotient.mk P) with hWdef
  set A := Localization.AtPrime W₀
  set J := P ⊔ Ideal.span {z} with hJdef
  let ψ : Localization.AtPrime W →+* A := Localization.localRingHom W W₀ (Ideal.Quotient.mk P) rfl

  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective W₀.primeCompl x
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨t', ht'⟩ := Ideal.Quotient.mk_surjective (t : S ⧸ P)
    have hs : t' ∈ W.primeCompl := by
      intro h
      apply t.2
      rw [← ht']
      exact h
    refine ⟨IsLocalization.mk' _ a' ⟨t', hs⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext ht'

  have hker : Ideal.comap ψ ⊥ ≤ J.map (algebraMap S (Localization.AtPrime W)) := by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl x
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨t, ht⟩, htr⟩ := hx
    obtain ⟨t', rfl⟩ := Ideal.Quotient.mk_surjective t
    have ht'W : t' ∈ W.primeCompl := ht
    have hmemP : t' * r ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
      exact htr
    have hrJ : algebraMap S (Localization.AtPrime W) r ∈ J.map (algebraMap S (Localization.AtPrime W)) := by
      rw [← Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units (Localization.AtPrime W) ⟨_, ht'W⟩),
        ← map_mul]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_left hmemP)
    show IsLocalization.mk' (Localization.AtPrime W) r s ∈ _
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ hrJ

  have hcomp : ψ.comp (algebraMap S (Localization.AtPrime W)) =
      (algebraMap (S ⧸ P) A).comp (Ideal.Quotient.mk P) :=
    RingHom.ext fun x => Localization.localRingHom_to_map W W₀ (Ideal.Quotient.mk P) rfl x
  have hJmk : J.map (Ideal.Quotient.mk P) = Ideal.span {Ideal.Quotient.mk P z} := by
    rw [hJdef, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, Set.image_singleton]
  have hI : (J.map (algebraMap S (Localization.AtPrime W))).map ψ =
      Ideal.span {algebraMap (S ⧸ P) A (Ideal.Quotient.mk P z)} := by
    rw [Ideal.map_map, hcomp, ← Ideal.map_map, hJmk, Ideal.map_span, Set.image_singleton]
  let : CommRing A := inferInstance
  let g := (Ideal.Quotient.mk (Ideal.span {algebraMap (S ⧸ P) A (Ideal.Quotient.mk P z)})).comp ψ
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hψ
  have hgk : J.map (algebraMap S (Localization.AtPrime W)) = RingHom.ker g := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, ← hI, Ideal.comap_map_of_surjective _ hψ, sup_eq_left.mpr hker]
  have key := length_self_eq_of_ringEquiv'
    ((Ideal.quotEquivOfEq hgk).trans (RingHom.quotientKerEquivOfSurjective hg))
  rw [length_localizedModule_quot', key]
  exact (Module.length_eq_of_surjective Ideal.Quotient.mk_surjective).symm
end LocalizedQuotLength
end GroundTheory.Heights₂.Heights.NumbersDVR

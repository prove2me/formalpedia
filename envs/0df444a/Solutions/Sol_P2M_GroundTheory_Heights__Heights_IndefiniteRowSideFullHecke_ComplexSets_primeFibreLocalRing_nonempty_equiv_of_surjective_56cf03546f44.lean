-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_primeFibreLocalRing_nonempty_equiv_of_surjective_56cf03546f44
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:33:10.270859+00:00
-- url     : https://prove2.me/submissions/231f0636-ea58-44c9-9edf-32718ffe182e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFormalFibreQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFormalFibreQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R R'] [Algebra S S'] (f : R →+* S) (φ : R' →+* S')
    (hf : Function.Surjective f) (hφ : Function.Surjective φ)
    (hcomm : φ.comp (algebraMap R R') = (algebraMap S S').comp f)
    (hker : RingHom.ker φ ≤ (RingHom.ker f).map (algebraMap R R'))
    (P : Ideal S') [P.IsPrime] :
    Nonempty (primeFibreLocalRing S P ≃+* primeFibreLocalRing R (P.comap φ)) := by
  set q := P.comap (algebraMap S S') with hq
  have hq' : (P.comap φ).comap (algebraMap R R') = q.comap f := by
    rw [hq, Ideal.comap_comap, Ideal.comap_comap, hcomm]
  have hmapq : ((q.comap f).map (algebraMap R R')).map φ = q.map (algebraMap S S') := by
    rw [Ideal.map_map, hcomm, ← Ideal.map_map, Ideal.map_comap_of_surjective f hf]
  let ψ : Localization.AtPrime (P.comap φ) →+* Localization.AtPrime P :=
    Localization.localRingHom (P.comap φ) P φ rfl
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
    obtain ⟨a', rfl⟩ := hφ a
    obtain ⟨t', ht'⟩ := hφ (t : S')
    have ht'' : t' ∈ (P.comap φ).primeCompl := by
      change t' ∉ P.comap φ
      rw [Ideal.mem_comap, ht']
      exact t.2
    refine ⟨IsLocalization.mk' _ a' ⟨t', ht''⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext ht'
  let χ := (Ideal.Quotient.mk ((q.map (algebraMap S S')).map
    (algebraMap S' (Localization.AtPrime P)))).comp ψ
  have hχ : Function.Surjective χ := Ideal.Quotient.mk_surjective.comp hψ
  have hkerχ : ((q.comap f).map (algebraMap R R')).map
      (algebraMap R' (Localization.AtPrime (P.comap φ))) = RingHom.ker χ := by
    ext x
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (P.comap φ).primeCompl x
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
      Localization.localRingHom_mk', IsLocalization.mk'_mem_map_algebraMap_iff,
      IsLocalization.mk'_mem_map_algebraMap_iff]
    constructor
    · rintro ⟨t, ht, htr⟩
      refine ⟨φ t, ht, ?_⟩
      rw [← map_mul, ← hmapq]
      exact Ideal.mem_map_of_mem φ htr
    · rintro ⟨t, ht, htr⟩
      obtain ⟨t', rfl⟩ := hφ t
      refine ⟨t', ht, ?_⟩
      have h1 : φ (t' * r) ∈ ((q.comap f).map (algebraMap R R')).map φ := by
        rw [hmapq, map_mul]
        exact htr
      rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective φ hφ] at h1
      have key : Ideal.comap φ ⊥ ≤ (q.comap f).map (algebraMap R R') := by
        refine le_trans ?_ (le_trans hker (Ideal.map_mono ?_))
        · intro y hy
          simpa using hy
        · intro y hy
          rw [Ideal.mem_comap, RingHom.mem_ker.mp hy]
          exact q.zero_mem
      exact (sup_le le_rfl key) h1
  refine ⟨(((Ideal.quotEquivOfEq ?_).trans (RingHom.quotientKerEquivOfSurjective hχ))).symm⟩
  rw [← hkerχ, hq']
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

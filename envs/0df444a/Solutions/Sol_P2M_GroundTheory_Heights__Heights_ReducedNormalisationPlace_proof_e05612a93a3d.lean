-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ReducedNormalisationPlace_proof_e05612a93a3d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:07:45.935817+00:00
-- url     : https://prove2.me/submissions/036ec42b-b3bd-4c73-a858-7790fcffac48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StReducedNormalisationPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMinimalPrimePlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PReducedNormalisationPlace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ReducedNormalisationPlace_fracMap_mk__eq_zero_iff_b3c2a6f3b1b5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ReducedNormalisationPlace_eq_zero_of_forall_num_mem_d33df6b8804f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ReducedNormalisationPlace_exists_idempotent_98edc89d8fdf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_fracMap_unit_ede7a277c87b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_localization_ringEquiv_bf72767a7e08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_isIntegral_mul_of_fracMap_31178a133ad5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_normMap_algebraMap_558ef40ab02f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ord_ringEquiv_ad3b8618db20


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
open MvPolynomial ComplexSets MinimalPrimePlace
noncomputable section
open ReducedNormalisationPlace
namespace GroundTheory.Heights₂.Heights
namespace ReducedNormalisationPlace
theorem _root_.solution : ReducedNormalisationPlace.Statement := by
  intro R _ _ _ P
  have hfin := minimalPrimes.finite_of_isNoetherianRing R
  have := P.isMaximal.isPrime
  choose! e he using fun p (hp : p ∈ minimalPrimes R) ↦ exists_idempotent p hp
  have hprodK : ∏ p ∈ hfin.toFinset, (1 - (e p : FractionRing R)) = 0 := by
    refine eq_zero_of_forall_num_mem _ fun p hp a u hz ↦ ?_
    have := hp.1.1
    have hk : RingHom.ker (Ideal.Quotient.mk p) ∈ minimalPrimes R := by rwa [Ideal.mk_ker]
    have h0 : fracMap (Ideal.Quotient.mk p) hk (∏ q ∈ hfin.toFinset, (1 - (e q : FractionRing R))) = 0 := by
      rw [map_prod]
      refine Finset.prod_eq_zero (hfin.mem_toFinset.2 hp) ?_
      rw [map_sub, map_one,
        (he p hp (R ⧸ p) (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective Ideal.mk_ker).1, sub_self]
    rw [hz, fracMap_mk'_eq_zero_iff, Ideal.mk_ker] at h0
    exact h0
  have hprod : ∏ p ∈ hfin.toFinset, (1 - e p) = 0 := Subtype.ext (by push_cast; exact hprodK)
  obtain ⟨p, hpT, hp1⟩ := (Ideal.IsPrime.prod_mem_iff (p := P.asIdeal)).1
    (by rw [hprod]; exact P.asIdeal.zero_mem)
  have hpmin : p ∈ minimalPrimes R := hfin.mem_toFinset.1 hpT
  have hepP : e p ∉ P.asIdeal := fun h ↦
    P.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using P.asIdeal.add_mem h hp1))
  refine ⟨p, hpmin, fun S _ φ hφ hkerφ ↦ ?_⟩
  have hpr : (RingHom.ker φ).IsPrime := hkerφ ▸ hpmin.1.1
  have : IsDomain S :=
    MulEquiv.isDomain (R ⧸ RingHom.ker φ) (RingHom.quotientKerEquivOfSurjective hφ).symm.toMulEquiv
  have hker : RingHom.ker φ ∈ minimalPrimes R := by rw [hkerφ]; exact hpmin
  obtain ⟨he1, hek⟩ := he p hpmin S φ hφ hkerφ
  obtain ⟨_, -, -, hsurj⟩ := exists_fracMap_unit φ hφ hker
  have hN : Function.Surjective (normMap φ hker) := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    have hint : IsIntegral R ((e p : FractionRing R) * x) :=
      isIntegral_mul_of_fracMap φ hφ hker he1 hek (by rw [hx]; exact y.2)
    refine ⟨⟨_, hint⟩, Subtype.ext ?_⟩
    show fracMap φ hker ((e p : FractionRing R) * x) = y
    rw [map_mul, he1, one_mul, hx]
  have hε1 : normMap φ hker (e p) = 1 := Subtype.ext he1
  have hε : ∀ z, normMap φ hker z = 0 → e p * z = 0 := fun z hz ↦
    Subtype.ext (hek z (congrArg Subtype.val hz))
  have hkerP : RingHom.ker (normMap φ hker) ≤ P.asIdeal := fun z hz ↦
    (P.isMaximal.isPrime.mem_or_mem (by rw [hε z hz]; exact P.asIdeal.zero_mem)).resolve_left hepP
  have hcm : (P.asIdeal.map (normMap φ hker)).comap (normMap φ hker) = P.asIdeal := by
    rw [Ideal.comap_map_of_surjective _ hN, ← RingHom.ker_eq_comap_bot, sup_eq_left.2 hkerP]
  have hmax : (P.asIdeal.map (normMap φ hker)).IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective _ hN P.isMaximal).resolve_left fun h ↦
      P.isMaximal.ne_top (by rw [← hcm, h, Ideal.comap_top])
  obtain ⟨E, hE⟩ := exists_localization_ringEquiv (normMap φ hker) hN (e p) hε1 hε
    (P.asIdeal.map (normMap φ hker))
  refine ⟨⟨_, hmax⟩, fun x ↦ ?_⟩
  have key : ∀ (Q : Ideal (integralClosure R (FractionRing R))) [Q.IsPrime], Q = P.asIdeal →
      ∀ E' : Localization.AtPrime Q ≃+* Localization.AtPrime (P.asIdeal.map (normMap φ hker)),
        (∀ r, E' (algebraMap _ _ r) = algebraMap _ _ (normMap φ hker r)) →
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap _ (Localization.AtPrime P.asIdeal) (algebraMap R (integralClosure R (FractionRing R)) x)) =
          Ring.ord (Localization.AtPrime (P.asIdeal.map (normMap φ hker)))
            (algebraMap _ (Localization.AtPrime (P.asIdeal.map (normMap φ hker)))
              (algebraMap S (integralClosure S (FractionRing S)) (φ x))) := by
    rintro Q _ rfl E' hE'
    rw [← ord_ringEquiv (R := Localization.AtPrime P.asIdeal)
      (S := Localization.AtPrime (P.asIdeal.map (normMap φ hker))) E', hE', normMap_algebraMap]
  exact key _ hcm E hE
end ReducedNormalisationPlace
end GroundTheory.Heights₂.Heights

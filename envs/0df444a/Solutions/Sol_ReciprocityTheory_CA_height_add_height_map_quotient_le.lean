-- Prove2me | solution 1 for ReciprocityTheory.CA.height_add_height_map_quotient_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:24:05.62721+00:00
-- url     : https://prove2.me/submissions/346d93b1-681e-4eb8-b256-9bef451383dd

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_IsSaturatedChain
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_RingKrullDimLocalizationQuotientEqHeight
import Theorems.Thm_ReciprocityTheory_CA_height_add_height_Ici_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.CA
open IsLocalRing
private theorem height_eq_order_height_lemma {R : Type*} [CommRing R] (I : Ideal R)
    [hI : I.IsPrime] : I.height = Order.height (⟨I, hI⟩ : PrimeSpectrum R) := by
  have hmin : I.minimalPrimes = {I} := Ideal.minimalPrimes_eq_subsingleton_self
  unfold Ideal.height
  apply le_antisymm
  · exact iInf₂_le I (by rw [hmin]; rfl)
  · refine le_iInf₂ fun J hJ => ?_
    have hJI : J = I := by rw [hmin] at hJ; exact hJ
    subst hJI
    exact le_rfl
end ReciprocityTheory.CA
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing
namespace ReciprocityTheory.CA
theorem _root_.solution {P : Type*} [CommRing P] (p q : Ideal P) [p.IsPrime]
    [q.IsPrime] (hpq : p ≤ q) : p.height + (q.map (Ideal.Quotient.mk p)).height ≤ q.height := by
  haveI hq' : (q.map (Ideal.Quotient.mk p)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hpq)
  rw [height_eq_order_height_lemma p, height_eq_order_height_lemma q,
    height_eq_order_height_lemma (q.map (Ideal.Quotient.mk p))]
  have hpq' : (⟨p, ‹_›⟩ : PrimeSpectrum P) ≤ ⟨q, ‹_›⟩ := hpq

  let f : PrimeSpectrum (P ⧸ p) → Set.Ici (⟨p, ‹_›⟩ : PrimeSpectrum P) := fun x =>
    ⟨⟨Ideal.comap (Ideal.Quotient.mk p) x.asIdeal, inferInstance⟩, fun z hz => by
      show z ∈ Ideal.comap (Ideal.Quotient.mk p) x.asIdeal
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hz]
      exact x.asIdeal.zero_mem⟩
  have hf : StrictMono f := by
    intro x y hxy
    show Ideal.comap (Ideal.Quotient.mk p) x.asIdeal < Ideal.comap (Ideal.Quotient.mk p) y.asIdeal
    refine lt_of_le_of_ne (Ideal.comap_mono (show x.asIdeal ≤ y.asIdeal from hxy.le)) fun e => ?_
    exact hxy.ne (PrimeSpectrum.ext
      (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective e))
  have hfq : f ⟨q.map (Ideal.Quotient.mk p), hq'⟩ = ⟨⟨q, ‹_›⟩, hpq'⟩ := by
    apply Subtype.ext
    apply PrimeSpectrum.ext
    show Ideal.comap (Ideal.Quotient.mk p) (q.map (Ideal.Quotient.mk p)) = q
    ext z
    rw [Ideal.mem_comap]
    first
    | exact Ideal.mem_quotient_iff_mem hpq
    | exact Ideal.mem_quotient_iff_mem_sup.trans (by rw [sup_eq_left.mpr hpq])
  have hle := Order.height_le_height_apply_of_strictMono f hf ⟨q.map (Ideal.Quotient.mk p), hq'⟩
  rw [hfq] at hle
  exact (add_le_add le_rfl hle).trans (height_add_height_Ici_le hpq')
end ReciprocityTheory.CA

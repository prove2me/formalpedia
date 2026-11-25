-- Prove2me | solution 1 for ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:17:32.526832+00:00
-- url     : https://prove2.me/submissions/18a2e382-6d4d-4291-8494-4af8ca07031f

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_IsSaturatedChain
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Theorems.Thm_ReciprocityTheory_CA_exists_ltSeries_lift_of_isIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
namespace ReciprocityTheory.CA
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B)) :
    ringKrullDim B = ringKrullDim A := by
  have hmono : StrictMono (fun q : PrimeSpectrum B =>
      (⟨q.asIdeal.comap (algebraMap A B), inferInstance⟩ : PrimeSpectrum A)) := by
    intro q q' hqq'
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hqq' ⊢
    obtain ⟨x, hx, hx'⟩ := SetLike.exists_of_lt hqq'
    exact Ideal.comap_lt_comap_of_integral_mem_sdiff (le_of_lt hqq') ⟨hx, hx'⟩
      (Algebra.IsIntegral.isIntegral x)
  apply le_antisymm
  · first
    | exact Order.krullDim_le_of_strictMono _ hmono
    | (apply iSup_le
       intro l'
       exact le_iSup_of_le (l'.map _ hmono) le_rfl)
  · apply iSup_le
    intro l
    obtain ⟨l', hlen, -⟩ := exists_ltSeries_lift_of_isIntegral hinj l
    rw [← hlen]
    exact le_iSup (fun p : LTSeries (PrimeSpectrum B) => (p.length : WithBot ℕ∞)) l'
end ReciprocityTheory.CA

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.WA.isUnitIn_div_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:12.470425+00:00
-- url     : https://prove2.me/submissions/f107e17c-2094-49d7-9847-0387895be8ea

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsNormOneOfPair
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_AlgebraMapNeZeroOfMemHcompl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_mem_hcompl_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_algebraMap_ne_zero_of_mem_hcompl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_mem_locR_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_mem_locRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace ReciprocityTheory.ChartRestriction.L3.WA
theorem _root_.solution {p : Ideal (𝓞 K)} (hp : p.IsPrime) (r : 𝓞 K) {s : 𝓞 K}
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) :
    IsUnitIn (locRing p) (algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s) ↔
      r ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
  have hsne := algebraMap_ne_zero_of_mem_hcompl hp hs
  unfold IsUnitIn
  constructor
  · rintro ⟨hne, -, hinv⟩
    have hrne : algebraMap (𝓞 K) K r ≠ 0 := fun h => hne (by rw [h, zero_div])
    rw [inv_div, mem_locRing, mem_locR_iff hp] at hinv
    obtain ⟨r', s', hs', he⟩ := hinv
    have hs'ne := algebraMap_ne_zero_of_mem_hcompl hp hs'
    rw [div_eq_div_iff hrne hs'ne] at he
    have he' : s * s' = r' * r := IsFractionRing.injective (𝓞 K) K (by rw [map_mul, map_mul, he])
    have hm : s * s' ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := mul_mem hs hs'
    rw [mem_hcompl_iff hp, he'] at hm
    rw [mem_hcompl_iff hp]
    exact ⟨fun h => hm.1 (Ideal.mul_mem_left _ _ h), fun h => hm.2 (Ideal.mul_mem_left _ _ h)⟩
  · intro hr
    have hrne := algebraMap_ne_zero_of_mem_hcompl hp hr
    refine ⟨div_ne_zero hrne hsne, ?_, ?_⟩
    · rw [mem_locRing, mem_locR_iff hp]
      exact ⟨r, s, hs, rfl⟩
    · rw [inv_div, mem_locRing, mem_locR_iff hp]
      exact ⟨s, r, hr, rfl⟩
end ReciprocityTheory.ChartRestriction.L3.WA

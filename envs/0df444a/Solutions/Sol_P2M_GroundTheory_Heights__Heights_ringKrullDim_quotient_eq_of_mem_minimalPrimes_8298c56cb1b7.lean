-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_eq_of_mem_minimalPrimes_8298c56cb1b7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:40.281353+00:00
-- url     : https://prove2.me/submissions/5895805b-e33a-470f-9475-5817878e49b1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CMDepthAssoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_length_le_ringKrullDim_quotient_colon_ae566819edbc

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
open IsLocalRing RingTheory.Sequence Pointwise
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {B : Type*} [CommRing B] [IsCohenMacaulayLocalRing B]
    {P : Ideal B} (hP : P ∈ minimalPrimes B) : ringKrullDim (B ⧸ P) = ringKrullDim B := by
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
  have hann : Module.annihilator B B = ⊥ := Module.annihilator_eq_bot.mpr inferInstance
  have hP' : P ∈ (Module.annihilator B B).minimalPrimes := by
    rw [hann]
    exact hP
  have hA := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes B B hP'
  obtain ⟨hprime, y, hy⟩ := (isAssociatedPrime_iff.mp hA)
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hprime.ne_top
    rw [hy, eq_top_iff]
    intro r _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem _
  have hD := length_le_ringKrullDim_quotient_colon rs y hy0 hm hreg
  rw [← hy, ← hdim] at hD
  exact le_antisymm (ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective) hD
end GroundTheory.Heights₂.Heights

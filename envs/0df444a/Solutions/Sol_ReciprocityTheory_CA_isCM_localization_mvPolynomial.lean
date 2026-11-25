-- Prove2me | solution 1 for ReciprocityTheory.CA.isCM_localization_mvPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:55:29.522142+00:00
-- url     : https://prove2.me/submissions/63b139f5-3db4-4c0f-aba6-0c3b59c0d0ec

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolySeq
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_RingKrullDimLocalizationQuotientEqHeight
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyCM
import Theorems.Thm_ReciprocityTheory_CA_depthGE_localization_of_isWeaklyRegular
import Theorems.Thm_ReciprocityTheory_CA_exists_isWeaklyRegular_mvPolynomial
import Theorems.Thm_ReciprocityTheory_CA_length_le_height_of_isWeaklyRegular


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing
namespace ReciprocityTheory.CA
theorem _root_.solution {P : Type*} [CommRing P] [IsLocalRing P] (hP : IsCM P) (N : ℕ)
    (𝔑 : Ideal (MvPolynomial (Fin N) P)) [𝔑.IsMaximal]
    (h : 𝔑.comap MvPolynomial.C = maximalIdeal P) :
    IsCM (Localization.AtPrime 𝔑) ∧ (𝔑.height : WithBot ℕ∞) = ringKrullDim P + N := by
  obtain ⟨hnoeth, n, hdim, rs, hlen, hmem, hreg⟩ := hP
  haveI := hnoeth
  obtain ⟨ss, hsslen, hssmem, hssreg⟩ :=
    exists_isWeaklyRegular_mvPolynomial hmem hreg.toIsWeaklyRegular N 𝔑 h
  have hle : ((rs.length + N : ℕ) : ℕ∞) ≤ 𝔑.height := by
    rw [← hsslen]; exact length_le_height_of_isWeaklyRegular 𝔑 hssmem hssreg
  have hge : (𝔑.height : WithBot ℕ∞) ≤ ringKrullDim P + N := by
    calc (𝔑.height : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin N) P) :=
          Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsMaximal.ne_top ‹_›)
      _ = ringKrullDim P + N := by
          rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, Nat.card_eq_fintype_card,
            Fintype.card_fin]
  have hht : (𝔑.height : WithBot ℕ∞) = ((n + N : ℕ) : WithBot ℕ∞) := by
    apply le_antisymm
    · rw [hdim] at hge
      exact_mod_cast hge
    · rw [hlen] at hle
      exact_mod_cast hle
  refine ⟨⟨?_, n + N, ?_, ?_⟩, ?_⟩
  · exact IsLocalization.isNoetherianRing 𝔑.primeCompl _ inferInstance
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔑, hht]
  · have := depthGE_localization_of_isWeaklyRegular 𝔑 hssmem hssreg
    rwa [hsslen, hlen] at this
  · rw [hht, hdim]
    push_cast
    rfl
end ReciprocityTheory.CA

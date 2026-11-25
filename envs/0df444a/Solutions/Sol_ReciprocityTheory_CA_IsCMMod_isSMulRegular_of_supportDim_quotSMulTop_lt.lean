-- Prove2me | solution 1 for ReciprocityTheory.CA.IsCMMod.isSMulRegular_of_supportDim_quotSMulTop_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:39:31.766091+00:00
-- url     : https://prove2.me/submissions/2236d787-63be-4d0b-a597-5417add17a03

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularAppendOfModDepthGE
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_AssDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Unmixed
import Theorems.Thm_ReciprocityTheory_CA_IsCMMod_ringKrullDim_quotient_eq_supportDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence
variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
private theorem unm_dim_le_of_le {I J : Ideal R} (h : I ≤ J) :
    ringKrullDim (R ⧸ J) ≤ ringKrullDim (R ⧸ I) := by
  refine ringKrullDim_le_of_surjective
    (Ideal.Quotient.lift I (Ideal.Quotient.mk J)
      (fun y hy => Ideal.Quotient.eq_zero_iff_mem.mpr (h hy))) ?_
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨Ideal.Quotient.mk I y, rfl⟩
end ReciprocityTheory.CA
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence
variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
namespace ReciprocityTheory.CA
namespace IsCMMod
theorem _root_.solution (h : IsCMMod R M) {x : R}
    (hd : Module.supportDim R (QuotSMulTop x M) < Module.supportDim R M) :
    IsSMulRegular M x := by
  obtain ⟨hR, hfin, n, hdim, hdep⟩ := id h
  haveI := hR
  haveI := hfin
  by_contra hx
  have hmem : x ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
    rw [biUnion_associatedPrimes_eq_compl_regular]
    exact hx
  simp only [Set.mem_iUnion, SetLike.mem_coe] at hmem
  obtain ⟨p, hp, hxp⟩ := hmem
  have hpp : p.IsPrime := IsAssociatedPrime.isPrime hp
  have hann : Module.annihilator R M ≤ p := by
    first
    | (have h0 := IsAssociatedPrime.annihilator_le hp
       rwa [Submodule.annihilator_top] at h0)
    | exact Submodule.annihilator_top (R := R) (M := M) ▸ IsAssociatedPrime.annihilator_le hp
  have hsuppQ : (⟨p, hpp⟩ : PrimeSpectrum R) ∈ Module.support R (QuotSMulTop x M) := by
    rw [Module.support_quotSMulTop]
    refine ⟨?_, ?_⟩
    · rw [Module.mem_support_iff_of_finite]
      exact hann
    · simp [PrimeSpectrum.mem_zeroLocus, hxp]
  have hannQ : Module.annihilator R (QuotSMulTop x M) ≤ p :=
    Module.mem_support_iff_of_finite.mp hsuppQ
  have hsQ : Module.supportDim R (QuotSMulTop x M) =
      ringKrullDim (R ⧸ Module.annihilator R (QuotSMulTop x M)) := by
    first
    | exact Module.supportDim_eq_ringKrullDim_quotient_annihilator R (QuotSMulTop x M)
    | exact Module.supportDim_eq_ringKrullDim_quotient_annihilator
    | (rw [ringKrullDim_quotient]; unfold Module.supportDim; rw [Module.support_eq_zeroLocus])
  have hle := unm_dim_le_of_le hannQ
  rw [h.ringKrullDim_quotient_eq_supportDim hp, ← hsQ] at hle
  exact absurd hd (not_lt.mpr hle)
end IsCMMod
end ReciprocityTheory.CA

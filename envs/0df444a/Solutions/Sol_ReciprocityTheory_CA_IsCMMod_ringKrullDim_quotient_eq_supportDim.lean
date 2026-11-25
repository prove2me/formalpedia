-- Prove2me | solution 1 for ReciprocityTheory.CA.IsCMMod.ringKrullDim_quotient_eq_supportDim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:30:09.012414+00:00
-- url     : https://prove2.me/submissions/51c6b9a3-1c8a-488d-b673-93b86d6fc766

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularAppendOfModDepthGE
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_AssDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Unmixed
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_le_ringKrullDim_quotient_of_mem_associatedPrimes

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
theorem _root_.solution (h : IsCMMod R M) {p : Ideal R}
    (hp : p ∈ associatedPrimes R M) : ringKrullDim (R ⧸ p) = Module.supportDim R M := by
  obtain ⟨hR, hfin, n, hdim, hdep⟩ := id h
  haveI := hR
  haveI := hfin
  have hann : Module.annihilator R M ≤ p := by
    first
    | (have h0 := IsAssociatedPrime.annihilator_le hp
       rwa [Submodule.annihilator_top] at h0)
    | exact Submodule.annihilator_top (R := R) (M := M) ▸ IsAssociatedPrime.annihilator_le hp
  have hsupp : Module.supportDim R M = ringKrullDim (R ⧸ Module.annihilator R M) := by
    first
    | exact Module.supportDim_eq_ringKrullDim_quotient_annihilator R M
    | exact Module.supportDim_eq_ringKrullDim_quotient_annihilator
    | (rw [ringKrullDim_quotient]; unfold Module.supportDim; rw [Module.support_eq_zeroLocus])
  apply le_antisymm
  · rw [hsupp]
    exact unm_dim_le_of_le hann
  · rw [hdim]
    exact hdep.le_ringKrullDim_quotient_of_mem_associatedPrimes hp
end IsCMMod
end ReciprocityTheory.CA

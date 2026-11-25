-- Prove2me | solution 1 for ReciprocityTheory.CA.IsCMMod.associatedPrimes_eq_minimalPrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:38:05.379318+00:00
-- url     : https://prove2.me/submissions/59da5750-3309-454d-bfa5-3e9095445896

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
private theorem unm_dim_succ_le_of_lt {Q P : Ideal R} [Q.IsPrime] (h : Q < P) :
    ringKrullDim (R ⧸ P) + 1 ≤ ringKrullDim (R ⧸ Q) := by
  obtain ⟨a, haP, haQ⟩ := SetLike.exists_of_lt h
  have hx0 : (Ideal.Quotient.mk Q a : R ⧸ Q) ≠ 0 :=
    fun hx => haQ (Ideal.Quotient.eq_zero_iff_mem.mp hx)
  have hxreg : (Ideal.Quotient.mk Q a : R ⧸ Q) ∈ nonZeroDivisors (R ⧸ Q) :=
    mem_nonZeroDivisors_of_ne_zero hx0
  let g : R ⧸ Q →+* R ⧸ P := Ideal.Quotient.lift Q (Ideal.Quotient.mk P)
    (fun y hy => Ideal.Quotient.eq_zero_iff_mem.mpr (h.le hy))
  have hgx : g (Ideal.Quotient.mk Q a) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr haP
  let f : (R ⧸ Q) ⧸ Ideal.span {(Ideal.Quotient.mk Q a : R ⧸ Q)} →+* R ⧸ P :=
    Ideal.Quotient.lift (Ideal.span {(Ideal.Quotient.mk Q a : R ⧸ Q)}) g
      (fun y hy => by
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
        rw [map_mul, hgx, mul_zero])
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk Q y), rfl⟩
  have hle : ringKrullDim (R ⧸ P) ≤
      ringKrullDim ((R ⧸ Q) ⧸ Ideal.span {(Ideal.Quotient.mk Q a : R ⧸ Q)}) :=
    ringKrullDim_le_of_surjective f hf
  calc ringKrullDim (R ⧸ P) + 1
      ≤ ringKrullDim ((R ⧸ Q) ⧸ Ideal.span {(Ideal.Quotient.mk Q a : R ⧸ Q)}) + 1 := by
        first | gcongr | exact add_le_add_right hle 1
    _ ≤ ringKrullDim (R ⧸ Q) := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hxreg
end ReciprocityTheory.CA
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence
variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
namespace ReciprocityTheory.CA
namespace IsCMMod
theorem _root_.solution (h : IsCMMod R M) :
    associatedPrimes R M = (Module.annihilator R M).minimalPrimes := by
  obtain ⟨hR, hfin, n, hdim, -⟩ := id h
  haveI := hR
  haveI := hfin
  apply Set.Subset.antisymm
  · intro p hp
    have hpp : p.IsPrime := IsAssociatedPrime.isPrime hp
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
    have hp' : ringKrullDim (R ⧸ p) = (n : WithBot ℕ∞) :=
      (h.ringKrullDim_quotient_eq_supportDim hp).trans hdim
    refine ⟨⟨hpp, hann⟩, fun q hq hqp => ?_⟩
    by_contra hne
    have hlt : q < p := lt_of_le_of_ne hqp (fun e => hne (le_of_eq e.symm))
    haveI := hq.1
    have h1 := unm_dim_succ_le_of_lt hlt
    have h2 : ringKrullDim (R ⧸ q) ≤ (n : WithBot ℕ∞) := by
      calc ringKrullDim (R ⧸ q) ≤ ringKrullDim (R ⧸ Module.annihilator R M) :=
            unm_dim_le_of_le hq.2
        _ = (n : WithBot ℕ∞) := hsupp.symm.trans hdim
    rw [hp'] at h1
    have h3 := h1.trans h2
    have h4 : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by exact_mod_cast h3
    have h5 : n + 1 ≤ n := by exact_mod_cast h4
    omega
  · first
    | exact Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M
    | exact Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
    | exact minimalPrimes_annihilator_subset_associatedPrimes R M
    | exact minimalPrimes_annihilator_subset_associatedPrimes
    | exact associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M
    | exact Module.minimalPrimes_annihilator_subset_associatedPrimes
end IsCMMod
end ReciprocityTheory.CA

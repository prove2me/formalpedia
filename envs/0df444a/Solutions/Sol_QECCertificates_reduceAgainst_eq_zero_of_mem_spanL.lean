-- Prove2me | solution 1 for QECCertificates.reduceAgainst_eq_zero_of_mem_spanL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:32.6754+00:00
-- url     : https://prove2.me/submissions/da11274e-53ad-48b0-ae70-431130f95311

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
public import Theorems.Thm_QECCertificates_reduceAgainst_self_mem

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {D : List (PivRow n)} (hD : IsReduced D) {v : Vec n}
    (hv : v ∈ spanL (rowList D)) : reduceAgainst D v = 0 := by
  have hle : spanL (rowList D) ≤ Submodule.comap (reduceAgainstLin D) ⊥ := by
    rw [spanL, Submodule.span_le]
    intro x hx
    have hx' : x ∈ rowList D := hx
    obtain ⟨ri, hri, hri_eq⟩ := List.mem_map.mp hx'
    rw [SetLike.mem_coe, Submodule.mem_comap, Submodule.mem_bot, ← hri_eq]
    exact reduceAgainst_self_mem hD hri
  have hv' : (reduceAgainstLin D) v ∈ (⊥ : Submodule (ZMod 2) (Vec n)) := hle hv
  rw [Submodule.mem_bot] at hv'
  exact hv'
end QECCertificates

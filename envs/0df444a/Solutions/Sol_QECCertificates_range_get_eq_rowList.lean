-- Prove2me | solution 1 for QECCertificates.range_get_eq_rowList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:45:53.143854+00:00
-- url     : https://prove2.me/submissions/4cbcf9e1-60e5-4f32-9d46-8c78cfa0ce9b

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
open _root_.Matrix
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (D : List (PivRow n)) :
    Set.range (fun i : Fin D.length => (D.get i).1) = {x | x ∈ rowList D} := by
  ext x
  rw [Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact List.mem_map_of_mem (List.get_mem D i)
  · intro hx
    have hx' : x ∈ rowList D := hx
    rw [rowList, List.mem_map] at hx'
    obtain ⟨ri, hri, rfl⟩ := hx'
    rw [List.mem_iff_get] at hri
    obtain ⟨i, rfl⟩ := hri
    exact ⟨i, rfl⟩
end QECCertificates

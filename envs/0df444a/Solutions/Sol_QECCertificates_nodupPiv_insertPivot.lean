-- Prove2me | solution 1 for QECCertificates.nodupPiv_insertPivot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:09.598081+00:00
-- url     : https://prove2.me/submissions/5ab01d86-f9f5-4ecf-b9af-1eb80f46966d

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Theorems.Thm_QECCertificates_map_piv_insertPivot

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
open _root_.Matrix
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {D : List (PivRow n)} (hD : NodupPiv D) {w : Vec n} {p : Fin n}
    (hp : p ∉ D.map (·.2)) : NodupPiv (insertPivot D w p) := by
  rw [NodupPiv, map_piv_insertPivot, List.nodup_append]
  refine ⟨hD, List.nodup_singleton p, ?_⟩
  intro a ha b hb
  rw [List.mem_singleton] at hb
  subst hb
  exact fun h => hp (h ▸ ha)
end QECCertificates

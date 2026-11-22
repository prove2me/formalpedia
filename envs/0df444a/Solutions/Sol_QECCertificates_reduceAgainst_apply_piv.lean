-- Prove2me | solution 1 for QECCertificates.reduceAgainst_apply_piv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:32.450475+00:00
-- url     : https://prove2.me/submissions/d7602cb3-4612-42e8-8093-61ca54004673

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Theorems.Thm_QECCertificates_reduceAgainst_cons
public import Theorems.Thm_QECCertificates_reduceAgainst_eq_zero_of_rows_zero
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_addSmul_zero_coord
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {D : List (PivRow n)} (hD : IsReduced D) (v : Vec n) :
    ∀ ri ∈ D, reduceAgainst D v ri.2 = 0 := by
  revert hD
  induction D generalizing v with
  | nil => intro _ ri hri; exact absurd hri (by simp)
  | cons r D ih =>
      intro hD
      have hD' : IsReduced D :=
        ⟨fun ri hri => hD.1 ri (List.mem_cons_of_mem r hri),
         fun ri hri rj hrj hne =>
           hD.2 ri (List.mem_cons_of_mem r hri) rj (List.mem_cons_of_mem r hrj) hne⟩
      rw [reduceAgainst_cons]
      intro ri hri
      rcases List.mem_cons.mp hri with hri_eq | hriD
      · rw [hri_eq]
        by_cases hrD : r ∈ D
        · exact ih _ hD' r hrD
        · refine reduceAgainst_eq_zero_of_rows_zero ?_
            (addSmul_zero_coord v r.1 r.2 (hD.1 r (List.mem_cons_self ..)))
          intro rk hrk
          exact hD.2 rk (List.mem_cons_of_mem r hrk) r (List.mem_cons_self ..)
            (fun h => hrD (h ▸ hrk))
      · exact ih _ hD' ri hriD
end QECCertificates

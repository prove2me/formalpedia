-- Prove2me | solution 1 for QECCertificates.IsReduced.pivot_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:44:56.280822+00:00
-- url     : https://prove2.me/submissions/4124843b-68c5-4817-bdcf-bf3d24b8f5b8

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
namespace IsReduced
theorem _root_.solution {D : List (PivRow n)} (h : IsReduced D) :
    ∀ ri ∈ D, ∀ rj ∈ D, ri.2 = rj.2 → ri = rj := by
  intro ri hri rj hrj hij
  by_contra hne
  have h1 := h.1 ri hri
  have h2 := h.2 ri hri rj hrj hne
  rw [← hij] at h2
  rw [h1] at h2
  exact one_ne_zero h2
end IsReduced
end QECCertificates

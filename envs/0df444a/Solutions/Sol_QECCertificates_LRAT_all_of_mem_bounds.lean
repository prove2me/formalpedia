-- Prove2me | solution 1 for QECCertificates.LRAT.all_of_mem_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:59.620376+00:00
-- url     : https://prove2.me/submissions/b535a262-4836-4e23-bdab-31abc71788c2

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {n : ℕ} {L : List (List Nat)}
    (h : (L.all fun r => r.all fun t => decide (t < n)) = true) :
    ∀ r ∈ L, ∀ t ∈ r, t < n := by
  intro r hr t ht
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h r hr) t ht)
end QECCertificates.LRAT

-- Prove2me | solution 1 for QECCertificates.LRAT.dotS_eq_false_iff_dotProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:05.025601+00:00
-- url     : https://prove2.me/submissions/932871ca-59b5-4583-9e14-f6de0b14da37

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
public import Theorems.Thm_QECCertificates_LRAT_dotS_eq_false_iff_even
public import Theorems.Thm_QECCertificates_LRAT_natCast_zmod2_eq_zero_iff_even
public import Theorems.Thm_QECCertificates_LRAT_dotProduct_rowOf_vecOf
public import Theorems.Thm_QECCertificates_LRAT_sum_indicator_eq_cntS

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution (σ : Assign) {n : ℕ} {r : List Nat}
    (hr : ∀ t ∈ r, t < n) (hrn : r.Nodup) :
    dotS σ r = false ↔ (rowOf n r) ⬝ᵥ (vecOf σ n) = 0 := by
  rw [dotS_eq_false_iff_even, ← natCast_zmod2_eq_zero_iff_even,
    ← sum_indicator_eq_cntS σ hr hrn, dotProduct_rowOf_vecOf]
end QECCertificates.LRAT

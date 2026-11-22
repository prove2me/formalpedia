-- Prove2me | solution 1 for QECCertificates.LRAT.satFormula_of_agree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:14.259019+00:00
-- url     : https://prove2.me/submissions/feeb2d45-5185-4272-bd14-36e6ade0ac96

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Theorems.Thm_QECCertificates_LRAT_satClause_of_agree

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {σ τ : Assign} {F : CNF} {c : Nat}
    (h : ∀ t, t < c → τ t = σ t) (hF : ∀ C ∈ F, ∀ l ∈ C, l.1 < c)
    (hσ : SatFormula σ F) : SatFormula τ F :=
  fun C hC => satClause_of_agree h (hF C hC) (hσ C hC)
end QECCertificates.LRAT

-- Prove2me | solution 1 for QECCertificates.LRAT.prodClauses_sat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:41.305058+00:00
-- url     : https://prove2.me/submissions/f3d7b38a-66f8-47c6-ba15-ea6f51059cc1

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Theorems.Thm_QECCertificates_LRAT_dotS_nil
public import Theorems.Thm_QECCertificates_LRAT_dotS_cons
public import Theorems.Thm_QECCertificates_LRAT_cntS_nil
public import Theorems.Thm_QECCertificates_LRAT_prod_sat
attribute [local simp] QECCertificates.LRAT.dotS_nil
attribute [local simp] QECCertificates.LRAT.dotS_cons
attribute [local simp] QECCertificates.LRAT.cntS_nil

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {σ : Assign} {c n : Nat}
    (h : ∀ C ∈ prodClauses c n, SatClause σ C) :
    ∀ j < n, σ (c + j) = (σ j && σ (n + j)) := by
  intro j hj
  have mem : ∀ C ∈ [[(c + j, false), (j, true)],
      [(c + j, false), (n + j, true)],
      [(c + j, true), (j, false), (n + j, false)]], C ∈ prodClauses c n := by
    intro C hC
    refine List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, ?_⟩
    exact hC
  exact prod_sat (h _ (mem _ (by simp)))
    (h _ (mem _ (by simp))) (h _ (mem _ (by simp)))
end QECCertificates.LRAT

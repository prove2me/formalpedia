-- Prove2me | solution 1 for QECCertificates.LRAT.chainFill_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:58:33.239937+00:00
-- url     : https://prove2.me/submissions/ee93cfef-8c17-4a86-a0cb-1cb505f3b09d

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Theorems.Thm_QECCertificates_LRAT_chainFill_cons

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {σ σ' : Assign} (rest : List Nat) (acc acc' : Bool) (c : Nat)
    (hacc : acc = acc') (h : ∀ t ∈ rest, σ t = σ' t) :
    ∀ t, chainFill σ rest acc c t = chainFill σ' rest acc' c t := by
  subst hacc
  induction rest generalizing acc c with
  | nil => intro t; rfl
  | cons x rest ih =>
      intro t
      have hx : σ x = σ' x := h x (List.mem_cons_self ..)
      have hrest : ∀ t' ∈ rest, σ t' = σ' t' := fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
      rw [chainFill_cons σ x rest acc c t, chainFill_cons σ' x rest acc c t, hx]
      by_cases ht : t = c
      · rw [if_pos ht, if_pos ht]
      · rw [if_neg ht, if_neg ht]
        exact ih (acc ^^ σ' x) (c + 1) hrest t
end QECCertificates.LRAT

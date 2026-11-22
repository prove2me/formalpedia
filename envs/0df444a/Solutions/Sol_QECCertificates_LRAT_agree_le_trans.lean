-- Prove2me | solution 1 for QECCertificates.LRAT.agree_le_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:56.815539+00:00
-- url     : https://prove2.me/submissions/d5ea437c-9911-48eb-bec6-ff3897027a37

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {σ τ υ : Assign} {a b : Nat}
    (h1 : ∀ t, t < b → τ t = σ t) (h2 : ∀ t, t < a → υ t = τ t) (h : a ≤ b) :
    ∀ t, t < a → υ t = σ t :=
  fun t ht => by rw [h2 t ht, h1 t (lt_of_lt_of_le ht h)]
end QECCertificates.LRAT

-- Prove2me | solution 1 for QECCertificates.LRAT.litFree_eq_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:29.11506+00:00
-- url     : https://prove2.me/submissions/e1d2b1be-05a4-43c0-96c5-9cb89605e39f

module
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic
public import Std.Data.TreeMap.Lemmas
public import Std.Data.DTreeMap.Lemmas
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {a : PAssign} {l : Lit} (h : litFree a l = false)
    {σ : Assign} (hσ : agrees σ a) : σ l.1 = !l.2 := by
  have hmem : litNeg l ∈ a := by
    by_contra hc
    simp [litFree, hc] at h
  have := hσ _ hmem
  simpa [litNeg] using this
end QECCertificates.LRAT

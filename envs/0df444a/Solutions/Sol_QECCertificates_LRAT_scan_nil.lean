-- Prove2me | solution 1 for QECCertificates.LRAT.scan_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:14.926657+00:00
-- url     : https://prove2.me/submissions/ebe92374-8922-4895-9c79-e79ef8637439

module
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic
public import Std.Data.TreeMap.Lemmas
public import Std.Data.DTreeMap.Lemmas
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Theorems.Thm_QECCertificates_LRAT_scanAux_spec

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {a : PAssign} {D : Clause} (h : scan a D = []) :
    ∀ l ∈ D, litFree a l = false := by
  obtain ⟨tail, h1, _, h3⟩ := scanAux_spec a D []
  have htail : tail = [] := by simpa [scan, h1] using h
  intro l hl
  by_cases hf : litFree a l = true
  · exact absurd (by rw [htail] at h3; exact h3 l hl hf) (by simp)
  · simpa using hf
end QECCertificates.LRAT

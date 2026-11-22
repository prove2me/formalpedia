-- Prove2me | solution 1 for QECCertificates.LRAT.scan_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:15.345617+00:00
-- url     : https://prove2.me/submissions/428bb7ce-5ed0-4e7c-901e-10812c8800cc

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
theorem _root_.solution {a : PAssign} {D : Clause} {l : Lit} (h : scan a D = [l]) :
    l ∈ D ∧ ∀ l' ∈ D, l' ≠ l → litFree a l' = false := by
  obtain ⟨tail, h1, h2, h3⟩ := scanAux_spec a D []
  have htail : tail = [l] := by simpa [scan, h1] using h
  refine ⟨(h2 l (by rw [htail]; simp)).1, ?_⟩
  intro l' hl' hne
  by_cases hf : litFree a l' = true
  · have hmem := h3 l' hl' hf
    rw [htail] at hmem
    exact absurd (List.mem_singleton.mp hmem) hne
  · simpa using hf
end QECCertificates.LRAT

-- Prove2me | solution 1 for QECCertificates.Submodule.mem_span_range_iff_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:03.269254+00:00
-- url     : https://prove2.me/submissions/eae4bb03-0024-4874-8ab5-7daa90436124

module
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
namespace QECCertificates
namespace Submodule
theorem _root_.solution {α : Type*} {n : ℕ} (x : Fin n → (ZMod 2)) (v : α → Fin n →
    (ZMod 2))
  : x ∈ Submodule.span (ZMod 2) (Set.range v) ↔ ∃ S : Finset α, ∑ s ∈ S, v s = x := by
  refine ⟨fun hx => ?_, ?_⟩
  · rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at hx
    obtain ⟨ c, rfl ⟩ := hx
    use c.support.filter (fun s => c s = 1)
    rw [ Finset.sum_filter ]; congr ; ext x i
    rcases Fin.exists_fin_two.mp ⟨ c x, rfl ⟩ with h | h
    · have h01 : ¬ ((0 : ZMod 2) = 1) := by norm_num
      rw [ h ]
      change (if (0 : ZMod 2) = 1 then v x i else 0) = (0 : ZMod 2) * v x i
      simp [ h01 ]
    · rw [ h ]
      change (if (1 : ZMod 2) = 1 then v x i else 0) = (1 : ZMod 2) * v x i
      simp
  · exact fun ⟨ S, hS ⟩ => hS ▸ Submodule.sum_mem _ fun i _ => Submodule.subset_span (
    Set.mem_range_self _ )
end Submodule
end QECCertificates

-- Prove2me | solution 1 for QECCertificates.exists_ker_dotProduct_eq_one_of_not_mem_rowSpace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:03.476713+00:00
-- url     : https://prove2.me/submissions/201c19e2-f7b1-4d45-8590-604e72df327c

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
public import Theorems.Thm_QECCertificates_mem_ker_iff_dotProd_rows_eq_zero
public import Theorems.Thm_QECCertificates_dual_eq_dotProduct

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
namespace QECCertificates
theorem _root_.solution {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod
    2))
    (x : Fin n → ZMod 2) (hx : x ∉ M.certificateRowSpace) :
    ∃ y ∈ LinearMap.ker M.toLin', y ⬝ᵥ x = 1 := by
  classical
  unfold Matrix.certificateRowSpace at hx
  let : Module.Free (ZMod 2) ((Fin n → ZMod 2) ⧸ Submodule.span (ZMod 2) (Set.range M)) :=
    Module.Free.of_basis (Module.Basis.ofVectorSpace (ZMod 2) _)
  obtain ⟨f, hfx, hf_bot⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
    (R := ZMod 2) (M := Fin n → ZMod 2) hx inferInstance
  refine ⟨fun i => f (Pi.single i 1), ?_, ?_⟩
  · rw [mem_ker_iff_dotProd_rows_eq_zero]
    intro i
    rw [dotProduct_comm]
    rw [← dual_eq_dotProduct]
    have : f (M i) ∈ Submodule.map f (Submodule.span (ZMod 2) (Set.range M)) :=
      Submodule.mem_map_of_mem (Submodule.subset_span (Set.mem_range_self i))
    rw [hf_bot] at this
    exact (Submodule.mem_bot _).mp this
  · -- Since $f x \neq 0$, we have $f x = 1$.
    have hfx_one : f x = 1 := by
      rcases Fin.exists_fin_two.mp ⟨ f x, rfl ⟩ with h | h
      · exact absurd h hfx
      · exact h
    convert hfx_one using 1
    convert dual_eq_dotProduct f x |> Eq.symm
end QECCertificates

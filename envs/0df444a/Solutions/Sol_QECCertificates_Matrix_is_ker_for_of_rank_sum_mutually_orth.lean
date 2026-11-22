-- Prove2me | solution 1 for QECCertificates.Matrix.is_ker_for_of_rank_sum_mutually_orth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:24.609572+00:00
-- url     : https://prove2.me/submissions/2206d9de-88b7-4ecf-b4db-6781188d72c7

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
namespace Matrix
theorem _root_.solution
  {k₁ k₂ r₁ r₂ n : ℕ}
  (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
  (hr₁ : r₁ ≤ M₁.rank)
  (hr₂ : r₂ ≤ M₂.rank)
  (hrn : r₁ + r₂ = n)
  (ho : M₁.certificateMutuallyOrthogonalRows M₂) :
  M₂.certificateIsKernelFor M₁ := by
    classical
    have h_dim_ker : Module.finrank (ZMod 2) (LinearMap.ker (Matrix.toLin' M₁)) = n - Matrix.rank
      M₁ := by
      have := LinearMap.finrank_range_add_finrank_ker (K := ZMod 2) (Matrix.mulVecLin M₁)
      exact eq_tsub_of_add_eq ( by norm_num at *; linarith! )
    have h_finrank_M₂ : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range M₂)) =
      Matrix.rank M₂ := by
      rw [Matrix.rank_eq_finrank_span_row M₂]
      congr 1
    have h_subspace : Submodule.span (ZMod 2) (Set.range M₂) ≤ LinearMap.ker (Matrix.toLin' M₁) :=
      by
      rw [ Submodule.span_le ]
      rintro _ ⟨i, rfl⟩
      change Matrix.mulVec M₁ (M₂ i) = 0
      exact funext fun j => by simpa [ Matrix.mulVec, dotProduct ] using ho j i
    have h_eq : Submodule.span (ZMod 2) (Set.range M₂) = LinearMap.ker (Matrix.toLin' M₁) := by
      exact Submodule.eq_of_le_of_finrank_le (K := ZMod 2) h_subspace ( by omega )
    exact h_eq
end Matrix
end QECCertificates

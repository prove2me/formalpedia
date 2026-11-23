-- Prove2me | solution 1 for PPSLattice.claim_4_11
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:51:29.15981+00:00
-- url     : https://prove2.me/submissions/66743d4c-2373-40d9-b490-8100cac2a4d2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PPSLattice_FigCompilerValid
import Theorems.Thm_PPSLattice_fig_static_part_compiler
import Theorems.Thm_PPSLattice_fig_dynamic_part_compiler
import Theorems.Thm_PPSLattice_fig_part_compiler_join
import Theorems.Thm_PPSLattice_fig_compiler_size_polynomial
open QAlgorithms.Complexity
set_option autoImplicit false

/-- Claim 4.11, reduced to its static output part, its dynamic linear-form output part,
sequential assembly of two output-part compilers, and polynomial output length of the size TM2. -/
theorem solution : ∃ (K : Str → RestrictedDec.Circuit) (sC : ℕ → ℕ → ℕ → ℕ → ℕ) (c : ℕ),
    PPSLattice.FigCompilerValid K sC ∧ ∀ lam N n q : ℕ,
      sC lam N n q ≤ (lam + n + n * Nat.clog 2 q + Nat.clog 2 N + Nat.clog 2 q + 2) ^ c := by
  obtain ⟨K₁, s₁, h₁⟩ := PPSLattice.fig_static_part_compiler
  obtain ⟨K₂, s₂, h₂⟩ := PPSLattice.fig_dynamic_part_compiler
  have hjoin : PPSLattice.FigPartCompilerValid
      (PPSLattice.figPartAdd PPSLattice.figPreOut PPSLattice.figDynamicOut)
      (PPSLattice.joinFigCompiler K₁ K₂) (PPSLattice.joinFigSize s₁ s₂) :=
    PPSLattice.fig_part_compiler_join PPSLattice.figPreOut PPSLattice.figDynamicOut
      K₁ K₂ s₁ s₂ h₁ h₂
  have hvalid : PPSLattice.FigCompilerValid
      (PPSLattice.joinFigCompiler K₁ K₂) (PPSLattice.joinFigSize s₁ s₂) := by
    rw [← PPSLattice.figPartCompilerValid_figOut, PPSLattice.figOut_eq_figPartAdd]
    exact hjoin
  obtain ⟨c, hc⟩ := PPSLattice.fig_compiler_size_polynomial
    (PPSLattice.joinFigCompiler K₁ K₂) (PPSLattice.joinFigSize s₁ s₂) hvalid
  exact ⟨PPSLattice.joinFigCompiler K₁ K₂, PPSLattice.joinFigSize s₁ s₂, c, hvalid, hc⟩

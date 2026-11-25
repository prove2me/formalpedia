-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.mem_span_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:57:30.92022+00:00
-- url     : https://prove2.me/submissions/e298c5ca-4b3d-4660-a2a1-b66c6ad87b8e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetOneAddSmulSingleSame
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_sum_single_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.II
theorem _root_.solution (Y : M2 n) (hY : Y.toBlocks₂₁ = 0) : Y ∈ Submodule.span ℂ (Gen n) := by
  have hE1 : ∀ i j (a : ℂ), (fromBlocks (Matrix.single i j a) 0 0 0 : M2 n) ∈ Submodule.span ℂ (Gen n) := by
    intro i j a
    have h : (fromBlocks (Matrix.single i j a) 0 0 0 : M2 n) =
        (a / 2) • (Pij 1 i j - Complex.I • Pij Complex.I i j) := by
      ext (p|p) (q|q)
      all_goals simp [Pij, Matrix.single_apply]
      all_goals split_ifs
      all_goals ring_nf
      all_goals simp [Complex.I_sq]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.subset_span (Or.inr ⟨1, i, j, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨Complex.I, i, j, rfl⟩))))
  have hE2 : ∀ i j (a : ℂ), (fromBlocks 0 0 0 (Matrix.single i j a) : M2 n) ∈ Submodule.span ℂ (Gen n) := by
    intro i j a
    have h : (fromBlocks 0 0 0 (Matrix.single i j a) : M2 n) =
        (-a / 2) • (Pij 1 j i + Complex.I • Pij Complex.I j i) := by
      ext (p|p) (q|q)
      all_goals simp [Pij, Matrix.single_apply]
      all_goals split_ifs
      all_goals ring_nf
      all_goals simp [Complex.I_sq]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _
      (Submodule.subset_span (Or.inr ⟨1, j, i, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨Complex.I, j, i, rfl⟩))))
  have hA : ∀ A, fb11 n A ∈ Submodule.span ℂ (Gen n) :=
    sum_single_mem _ (fb11 n) (fun i j a => hE1 i j a)
  have hD : ∀ D, fb22 n D ∈ Submodule.span ℂ (Gen n) :=
    sum_single_mem _ (fb22 n) (fun i j a => hE2 i j a)
  have hB : ∀ B : Matrix (Fin n) (Fin n) ℂ, (fromBlocks 0 B 0 0 : M2 n) ∈ Submodule.span ℂ (Gen n) := by
    intro B
    have hH1 : ((1 / 2 : ℂ) • (B + Bᴴ))ᴴ = (1 / 2 : ℂ) • (B + Bᴴ) := by
      ext p q
      simp [Matrix.conjTranspose_apply]
      ring
    have hH2 : ((-Complex.I / 2) • (B - Bᴴ))ᴴ = (-Complex.I / 2) • (B - Bᴴ) := by
      ext p q
      simp [Matrix.conjTranspose_apply]
      ring
    have hsplit : (fromBlocks 0 B 0 0 : M2 n) = fromBlocks 0 ((1 / 2 : ℂ) • (B + Bᴴ)) 0 0 +
        Complex.I • fromBlocks 0 ((-Complex.I / 2) • (B - Bᴴ)) 0 0 := by
      ext (p|p) (q|q)
      all_goals simp
      ring_nf
      simp [Complex.I_sq]
      ring
    rw [hsplit]
    exact Submodule.add_mem _ (Submodule.subset_span (Or.inl ⟨_, hH1, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨_, hH2, rfl⟩)))
  have hYe : Y = fb11 n Y.toBlocks₁₁ + fromBlocks 0 Y.toBlocks₁₂ 0 0 + fb22 n Y.toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks Y, hY]
    simp [fb11, fb22, Matrix.fromBlocks_add]
  rw [hYe]
  exact Submodule.add_mem _ (Submodule.add_mem _ (hA _) (hB _)) (hD _)
end PositivityTheory.Rg.Sw.LVs.II

-- Prove2me | solution 1 for VectorValuedHolomorphy.dense_setOf_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:57:14.559721+00:00
-- url     : https://prove2.me/submissions/144c0f74-077d-48b6-9ca8-ade63e79821e

import Mathlib

open Filter Topology Metric
open scoped Real

set_option autoImplicit false


theorem solution (𝕜 : Type*) [RCLike 𝕜] (X : Type*) [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] (E : Type*) [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E]
    [T2Space E] :
    Dense {f : C(X, E) | HasCompactSupport f} := by
  -- a cut-off function equal to `1` on each compact set
  have hχ : ∀ K : TopologicalSpace.Compacts X, ∃ χ : C(X, ℝ), Set.EqOn χ 1 K ∧
      HasCompactSupport χ := by
    intro K
    obtain ⟨χ, h1, -, h2, -⟩ := exists_continuous_one_zero_of_isCompact K.isCompact
      isClosed_empty (Set.disjoint_empty _)
    exact ⟨χ, h1, h2⟩
  choose χ hχ1 hχc using hχ
  intro f
  -- the approximating family `K ↦ χ_K • f`
  let F : TopologicalSpace.Compacts X → C(X, E) := fun K =>
    ⟨fun x => ((χ K x : ℝ) : 𝕜) • f x,
      ((RCLike.continuous_ofReal.comp (χ K).continuous).smul f.continuous)⟩
  have hF : ∀ K, HasCompactSupport (F K) := by
    intro K
    have h : HasCompactSupport (fun x => ((χ K x : ℝ) : 𝕜)) :=
      (hχc K).comp_left (by simp)
    exact h.smul_right (f' := fun x => f x)
  have hF1 : ∀ (K : TopologicalSpace.Compacts X) (x : X), x ∈ (K : Set X) → F K x = f x := by
    intro K x hx
    have : χ K x = 1 := hχ1 K hx
    simp [F, this]
  refine mem_closure_of_tendsto (f := F) (b := atTop) ?_ (Eventually.of_forall hF)
  rw [ContinuousMap.tendsto_compactOpen_iff_forall]
  intro L hL
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (⟨L, hL⟩ : TopologicalSpace.Compacts X)] with K hK
  ext x
  exact (hF1 K x (hK x.2)).symm

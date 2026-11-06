-- Prove2me | solution 1 for PrimalDualLDR.FixedRecourse.sec_2_2_constraints
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T17:43:42.689192+00:00
-- url     : https://prove2.me/submissions/97c4c21f-9c02-4249-89db-997f100bf1f5

import Mathlib
import Definitions.Def_PrimalDualLDR_FixedRecourse_Basic
import Definitions.Def_PrimalDualLDR_FixedRecourse_Setting
import Definitions.Def_PrimalDualLDR_FixedRecourse_Problems

open MeasureTheory Matrix

open PrimalDualLDR.FixedRecourse in
theorem solution (σ : Setting) (hσ : σ.Standing)
    (X : Matrix (Fin σ.n) (Fin σ.k) ℝ) (S : Matrix (Fin σ.m) (Fin σ.k) ℝ) :
    ((∀ᵐ ξ ∂σ.P, σ.A.mulVec (X.mulVec ξ) + S.mulVec ξ = σ.B.mulVec ξ) ↔
        ∀ ξ ∈ σ.Xi, σ.A.mulVec (X.mulVec ξ) + S.mulVec ξ = σ.B.mulVec ξ) ∧
    ((∀ᵐ ξ ∂σ.P, ∀ i, 0 ≤ (S.mulVec ξ) i) ↔ ∀ ξ ∈ σ.Xi, ∀ i, 0 ≤ (S.mulVec ξ) i) ∧
    ((∀ᵐ ξ ∂σ.P, σ.A.mulVec (X.mulVec ξ) + S.mulVec ξ = σ.B.mulVec ξ) ↔ σ.A * X + S = σ.B) := by
  obtain ⟨⟨_, hnull, hpos⟩, -, -, -, -, -, hspan⟩ := hσ
  have hXi : σ.Xi ∈ ae σ.P := mem_ae_iff.2 hnull
  -- a closed set of full measure contains the support
  have sub : ∀ C : Set (Fin σ.k → ℝ), IsClosed C → (∀ᵐ ξ ∂σ.P, ξ ∈ C) → σ.Xi ⊆ C := by
    intro C hC hae ξ hξ
    by_contra hξC
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hC.isOpen_compl ξ hξC
    have h0 : σ.P Cᶜ = 0 := by
      rw [← mem_ae_iff]; exact hae
    have := hpos ξ hξ ε hε
    exact absurd (measure_mono_null hball h0) this.ne'
  have gen : ∀ p : (Fin σ.k → ℝ) → Prop, IsClosed {ξ | p ξ} →
      ((∀ᵐ ξ ∂σ.P, p ξ) ↔ ∀ ξ ∈ σ.Xi, p ξ) := by
    intro p hp
    constructor
    · intro h ξ hξ; exact sub _ hp h hξ
    · intro h; exact Filter.mem_of_superset hXi h
  have hc1 : IsClosed {ξ : Fin σ.k → ℝ | σ.A.mulVec (X.mulVec ξ) + S.mulVec ξ = σ.B.mulVec ξ} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have hc2 : IsClosed {ξ : Fin σ.k → ℝ | ∀ i, 0 ≤ (S.mulVec ξ) i} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const
      ((continuous_apply i).comp (Continuous.matrix_mulVec continuous_const continuous_id))
  refine ⟨gen _ hc1, gen _ hc2, ?_⟩
  rw [gen _ hc1]
  have hrw : ∀ ξ, σ.A.mulVec (X.mulVec ξ) + S.mulVec ξ = (σ.A * X + S).mulVec ξ := by
    intro ξ; rw [add_mulVec, mulVec_mulVec]
  constructor
  · intro h
    have hker : σ.Xi ⊆ (LinearMap.ker (Matrix.toLin' (σ.A * X + S - σ.B)) : Set _) := by
      intro ξ hξ
      simp only [SetLike.mem_coe, LinearMap.mem_ker, toLin'_apply, sub_mulVec, ← hrw, h ξ hξ,
        sub_self]
    have htop := Submodule.span_le.2 hker
    rw [hspan, top_le_iff, LinearMap.ker_eq_top] at htop
    have : σ.A * X + S - σ.B = 0 := by
      apply Matrix.toLin'.injective; rw [htop, map_zero]
    exact sub_eq_zero.1 this
  · intro h ξ _
    rw [hrw, h]

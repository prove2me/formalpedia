-- Prove2me | solution 1 for PrimalDualLDR.FixedRecourse.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T17:45:20.731298+00:00
-- url     : https://prove2.me/submissions/244c9586-4d0d-43ae-a1b6-6555ac58d723

import Mathlib
import Definitions.Def_PrimalDualLDR_FixedRecourse_Basic
import Definitions.Def_PrimalDualLDR_FixedRecourse_Setting
import Definitions.Def_PrimalDualLDR_FixedRecourse_Problems

open MeasureTheory Matrix

namespace LDRAux
open PrimalDualLDR.FixedRecourse

lemma ae_mem_Xi (σ : Setting) (hσ : σ.Standing) : ∀ᵐ ξ ∂σ.P, ξ ∈ σ.Xi :=
  mem_ae_iff.2 hσ.1.2.1

lemma Xi_subset_of_closed (σ : Setting) (hσ : σ.Standing) (C : Set (Fin σ.k → ℝ))
    (hC : IsClosed C) (hae : ∀ᵐ ξ ∂σ.P, ξ ∈ C) : σ.Xi ⊆ C := by
  intro ξ hξ
  by_contra hξC
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hC.isOpen_compl ξ hξC
  have h0 : σ.P Cᶜ = 0 := by
    rw [← mem_ae_iff]; exact hae
  have := hσ.1.2.2 ξ hξ ε hε
  exact absurd (measure_mono_null hball h0) this.ne'

lemma exists_bound (σ : Setting) (hσ : σ.Standing) : ∃ R : ℝ, ∀ ξ ∈ σ.Xi, ‖ξ‖ ≤ R :=
  isBounded_iff_forall_norm_le.1 hσ.2.2.1

lemma ae_norm_le (σ : Setting) (hσ : σ.Standing) : ∃ R : ℝ, ∀ᵐ ξ ∂σ.P, ‖ξ‖ ≤ R := by
  obtain ⟨R, hR⟩ := exists_bound σ hσ
  exact ⟨R, (ae_mem_Xi σ hσ).mono fun ξ hξ => hR ξ hξ⟩

lemma ae_coord_le (σ : Setting) (hσ : σ.Standing) : ∃ R : ℝ, ∀ᵐ ξ ∂σ.P, ∀ j, ‖ξ j‖ ≤ R := by
  obtain ⟨R, hR⟩ := ae_norm_le σ hσ
  exact ⟨R, hR.mono fun ξ hξ j => (norm_le_pi_norm ξ j).trans hξ⟩

/-- an integrable function times a coordinate is integrable -/
lemma integrable_mul_coord (σ : Setting) (hσ : σ.Standing) {f : (Fin σ.k → ℝ) → ℝ}
    (hf : Integrable f σ.P) (j : Fin σ.k) : Integrable (fun ξ => f ξ * ξ j) σ.P := by
  obtain ⟨R, hR⟩ := ae_coord_le σ hσ
  exact hf.mul_bdd (continuous_apply j).aestronglyMeasurable (hR.mono fun ξ h => h j)

lemma integrable_coord (σ : Setting) (hσ : σ.Standing) (j : Fin σ.k) :
    Integrable (fun ξ : Fin σ.k → ℝ => ξ j) σ.P := by
  simpa using integrable_mul_coord σ hσ (integrable_const (1 : ℝ)) j

lemma integrable_coord_mul_coord (σ : Setting) (hσ : σ.Standing) (i j : Fin σ.k) :
    Integrable (fun ξ : Fin σ.k → ℝ => ξ i * ξ j) σ.P :=
  integrable_mul_coord σ hσ (integrable_coord σ hσ i) j

lemma M_symm (σ : Setting) : σ.Mᵀ = σ.M := by
  ext i j; simp only [transpose_apply, Setting.M, mul_comm]

end LDRAux

namespace LDRAux
open PrimalDualLDR.FixedRecourse

lemma quad_eq (σ : Setting) (hσ : σ.Standing) (v : Fin σ.k → ℝ) :
    v ⬝ᵥ (σ.M *ᵥ v) = ∫ ξ, (v ⬝ᵥ ξ) ^ 2 ∂σ.P := by
  have hpt : ∀ ξ : Fin σ.k → ℝ, (v ⬝ᵥ ξ) ^ 2 = ∑ i, ∑ j, v i * (ξ i * ξ j) * v j := by
    intro ξ
    simp only [dotProduct, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [hpt]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ =>
    ((integrable_coord_mul_coord σ hσ i j).const_mul (v i)).mul_const (v j))]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ (fun j _ =>
    ((integrable_coord_mul_coord σ hσ i j).const_mul (v i)).mul_const (v j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const, integral_const_mul]
  simp only [Setting.M]; ring

end LDRAux

open PrimalDualLDR.FixedRecourse LDRAux in
theorem solution (σ : Setting) (hσ : σ.Standing) : σ.M.PosDef ∧ IsUnit σ.M := by
  have hpd : σ.M.PosDef := by
    refine PosDef.of_dotProduct_mulVec_pos ?_ fun v hv => ?_
    · ext i j; simp only [conjTranspose_apply, star_trivial, Setting.M, mul_comm]
    · rw [star_trivial, quad_eq σ hσ v]
      have hint : Integrable (fun ξ : Fin σ.k → ℝ => (v ⬝ᵥ ξ) ^ 2) σ.P := by
        have : (fun ξ : Fin σ.k → ℝ => (v ⬝ᵥ ξ) ^ 2) =
            fun ξ => ∑ i, ∑ j, v i * (ξ i * ξ j) * v j := by
          funext ξ
          simp only [dotProduct, sq, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
        rw [this]
        exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
          ((integrable_coord_mul_coord σ hσ i j).const_mul (v i)).mul_const (v j)
      refine lt_of_le_of_ne (integral_nonneg fun ξ => sq_nonneg _) fun h0 => hv ?_
      have hae := (integral_eq_zero_iff_of_nonneg (fun ξ => sq_nonneg _) hint).1 h0.symm
      have hsub : σ.Xi ⊆ {ξ | v ⬝ᵥ ξ = 0} := by
        refine Xi_subset_of_closed σ hσ _ (isClosed_eq (by fun_prop) continuous_const) ?_
        filter_upwards [hae] with ξ hξ
        simpa using hξ
      have hker : σ.Xi ⊆ (LinearMap.ker (dotProductBilin ℝ ℝ v) : Set _) := by
        intro ξ hξ
        simpa using hsub hξ
      have htop := Submodule.span_le.2 hker
      rw [hσ.2.2.2.2.2.2, top_le_iff] at htop
      have hvv : v ⬝ᵥ v = 0 := by
        have : v ∈ LinearMap.ker (dotProductBilin ℝ ℝ v) := by rw [htop]; trivial
        simpa using this
      exact dotProduct_self_eq_zero.1 hvv
  exact ⟨hpd, hpd.isUnit⟩

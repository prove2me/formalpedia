-- Prove2me | solution 1 for PolyaLaplacian.polya_annulus
-- status  : ACCEPTED   (disprove)
-- author  : @Secousses
-- created : 2026-11-24T23:09:56.579552+00:00
-- url     : https://prove2.me/submissions/c28e1375-c235-45aa-82d7-faa316c4feaf

import Mathlib
import Definitions.Def_PolyaLaplacian_Spectral

set_option autoImplicit false

open MeasureTheory Set TopologicalSpace
open PolyaLaplacian

/-- As formalized, `dirichletEigenvalue Ω k = 0` for every `k ≥ 1`: in `ℝ`,
`⨅ (_ : finrank V = k), _` is `sInf ∅ = 0` whenever `finrank V ≠ k` (e.g. `V = ⊥`),
and every term of the outer infimum is `≥ 0`. -/
private lemma eig_zero {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) (hk : 1 ≤ k) :
    dirichletEigenvalue Ω k = 0 := by
  unfold dirichletEigenvalue
  have hnn : ∀ V : Submodule ℝ (TestFn Ω),
      0 ≤ ⨅ (_ : Module.finrank ℝ V = k),
        ⨆ (u : V) (_ : (u : TestFn Ω) ≠ 0), rayleighQuotient Ω (u : TestFn Ω) := by
    intro V
    apply Real.iInf_nonneg
    intro _
    apply Real.iSup_nonneg
    intro u
    by_cases hu : (u : TestFn Ω) = 0
    · simp [hu]
    · have : Nonempty ((u : TestFn Ω) ≠ 0) := ⟨hu⟩
      rw [ciSup_const]
      unfold rayleighQuotient dirichletEnergy l2Mass
      apply div_nonneg
      · exact setIntegral_nonneg_of_ae_restrict
          (Filter.Eventually.of_forall fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)
      · exact integral_nonneg fun x => sq_nonneg _
  apply le_antisymm
  · refine (ciInf_le ⟨0, ?_⟩ (⊥ : Submodule ℝ (TestFn Ω))).trans ?_
    · rintro _ ⟨V, rfl⟩; exact hnn V
    · have h : Module.finrank ℝ (⊥ : Submodule ℝ (TestFn Ω)) ≠ k := by
        rw [finrank_bot]; omega
      have : IsEmpty (Module.finrank ℝ (⊥ : Submodule ℝ (TestFn Ω)) = k) := ⟨h⟩
      rw [Real.iInf_of_isEmpty]
  · exact Real.iInf_nonneg hnn

private lemma area_pos_of {s : Set (EuclideanSpace ℝ (Fin 2))} (ho : IsOpen s)
    (hne : s.Nonempty) (hb : Bornology.IsBounded s) : 0 < area s := by
  unfold area
  exact ENNReal.toReal_pos (ho.measure_pos volume hne).ne' hb.measure_lt_top.ne

private lemma annulus_area_pos :
    0 < area (annulus (1/2) : Set (EuclideanSpace ℝ (Fin 2))) := by
  apply area_pos_of
  · exact (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  · refine ⟨EuclideanSpace.single 0 (3/4), ?_⟩
    show (1/2 : ℝ) < ‖_‖ ∧ ‖_‖ < 1
    rw [EuclideanSpace.norm_eq]; norm_num [Fin.sum_univ_two]
  · exact Metric.isBounded_ball.subset fun x hx => mem_ball_zero_iff.mpr hx.2

theorem solution : ¬ (∀ (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (k : ℕ) (hk : 1 ≤ k),
    dirichletEigenvalue (annulus r : Set (EuclideanSpace ℝ (Fin 2))) k ≥
      4 * Real.pi * (k : ℝ) / area (annulus r : Set (EuclideanSpace ℝ (Fin 2)))) := by
  intro h
  have h1 := h (1/2) (by norm_num) (by norm_num) 1 le_rfl
  rw [eig_zero _ 1 le_rfl] at h1
  have : 0 < 4 * Real.pi * ((1 : ℕ) : ℝ) / area (annulus (1/2) : Set (EuclideanSpace ℝ (Fin 2))) :=
    div_pos (by positivity) annulus_area_pos
  linarith

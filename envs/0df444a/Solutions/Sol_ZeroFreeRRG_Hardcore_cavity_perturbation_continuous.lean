-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.cavity_perturbation_continuous
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:55:04.078913+00:00
-- url     : https://prove2.me/submissions/ae3fdd8c-53f6-41b3-9071-36fe0ba32621

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (t : ℝ) (d : ℕ) :
    ContinuousOn (fun ν : ProbabilityMeasure (m.Spin → ℝ) =>
      (d:ℝ) * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1)^2)
        ∂(ν : Measure (m.Spin → ℝ))) (cavityLaws m t) := by
  classical
  let X := m.Spin → ℝ
  let φ : X → ℝ := fun μ => ∑ a, m.pi t a * (Mmul m t μ a - 1)^2
  have hφ : Continuous φ := by
    dsimp [φ]
    apply continuous_finset_sum
    intro a ha
    apply Continuous.const_mul
    apply Continuous.pow
    apply Continuous.sub
    · unfold Mmul
      apply continuous_finset_sum
      intro b hb
      exact (continuous_apply b).const_mul _
    · exact continuous_const
  let clip : X → X := fun x a => max 0 (min (x a) 1)
  have hclipcont : Continuous clip := by
    apply continuous_pi
    intro a
    exact continuous_const.max ((continuous_apply a).min continuous_const)
  have hclip (x : X) : clip x ∈ Icc (0 : X) 1 := by
    constructor <;> intro a
    · change (0:ℝ) ≤ max 0 (min (x a) 1)
      exact le_max_left _ _
    · change max 0 (min (x a) 1) ≤ (1:ℝ)
      exact max_le (by norm_num) (min_le_right _ _)
  have hc : IsCompact (φ '' Icc (0:X) 1) := isCompact_Icc.image hφ
  obtain ⟨C,hC⟩ := hc.isBounded.exists_norm_le
  let F : BoundedContinuousFunction X ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun x => φ (clip x), hφ.comp hclipcont⟩ (2*C) (by
      intro x y
      have hx := hC _ ⟨clip x,hclip x,rfl⟩
      have hy := hC _ ⟨clip y,hclip y,rfl⟩
      change dist (φ (clip x)) (φ (clip y)) ≤ 2*C
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans (by linarith))
  have hcont : Continuous (fun ν : ProbabilityMeasure X =>
      (d:ℝ) * ∫ x, F x ∂(ν : Measure X)) :=
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction F).const_mul _
  apply hcont.continuousOn.congr
  intro ν hν
  change (d:ℝ) * (∫ x, φ x ∂(ν : Measure X)) = (d:ℝ) * (∫ x, F x ∂(ν : Measure X))
  congr 1
  apply integral_congr_ae
  have hae : ∀ᵐ x ∂(ν : Measure X), x ∈ stdSimplex ℝ m.Spin := ae_iff.mpr hν.1
  filter_upwards [hae] with x hx
  change φ x = φ (clip x)
  congr 1
  funext a
  have h := mem_Icc_of_mem_stdSimplex hx a
  change x a = max 0 (min (x a) 1)
  rw [min_eq_left h.2, max_eq_right h.1]

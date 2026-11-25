-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.morseGen_uniform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:12:39.946806+00:00
-- url     : https://prove2.me/submissions/a0c952bd-31f7-43eb-88d4-989d0e4bb20a

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_MorseGenStA
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_MorseNormSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_TaylorLeviSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_MorseGenStB
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_exists_pluriharmonic_part
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_morseGen_ident
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_morseGen_levi_le
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_morseGen_sq_le_sum
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_morse_normal_uniform


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Complex Matrix Unitary
open scoped ComplexOrder
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {D : ℕ} {ρ₀ K₂ K₃ Lν νmin : ℝ} (hρ₀ : 0 < ρ₀) (hνmin : 0 < νmin) :
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ, 0 < n → ∀ (φ ν : (Fin D → ℂ) → ℝ) (f : (Fin D → ℂ) → ℂ),
      ContDiffOn ℝ 3 φ (Metric.ball 0 ρ₀) →
      ‖fderiv ℝ (fderiv ℝ φ) 0‖ ≤ K₂ →
      (∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, ‖iteratedFDeriv ℝ 3 φ z‖ ≤ K₃) →
      ContinuousOn ν (Metric.ball 0 ρ₀) → νmin ≤ ν 0 →
      (∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, ν 0 - Lν * ‖z‖ ≤ ν z) →
      (∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, 0 ≤ ν z) →
      DifferentiableOn ℂ f (Metric.ball 0 ρ₀) →
      IntegrableOn (fun z => ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z)
        (Metric.ball (0 : Fin D → ℂ) ρ₀) →
      ‖f 0‖ ^ 2 * Real.exp (-((n : ℝ) * φ 0)) ≤ M * (n : ℝ) ^ D *
        ∫ z in Metric.ball (0 : Fin D → ℂ) ρ₀, ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z := by
  set C : ℝ := max K₃ 0 + |Lν| / νmin with hCdef
  have hC : 0 ≤ C := by positivity
  obtain ⟨M₀, hM₀, hM⟩ := morse_normal_uniform (D := D) (ρ₀ := ρ₀) (C := C)
    (Λ := max K₂ 0 / 2) hρ₀ hC (by positivity)
  refine ⟨M₀ / νmin, by positivity, ?_⟩
  intro n hn φ ν f hφ hK₂ hK₃ hνc hνm hνL hνpos hf hint
  obtain ⟨q, hqd, hq0, hqb⟩ := exists_pluriharmonic_part φ hφ hK₃
  have hν0 : 0 < ν 0 := lt_of_lt_of_le hνmin hνm
  set g : (Fin D → ℂ) → ℝ := fun z => ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z with hg
  set c : ℝ := Real.exp ((n : ℝ) * φ 0) / ν 0 with hc
  set f' : (Fin D → ℂ) → ℂ := fun z => f z * cexp (-(n : ℂ) * q z / 2) with hf'
  set φ' : (Fin D → ℂ) → ℝ := fun z => φ z - φ 0 - (q z).re with hφ'
  set ν' : (Fin D → ℂ) → ℝ := fun z => ν z / ν 0 with hν'
  have hfun : (fun z => ‖f' z‖ ^ 2 * Real.exp (-((n : ℝ) * φ' z)) * ν' z) = fun z => g z * c := by
    funext z; exact morseGen_ident (f z) (q z) (φ z) (φ 0) (ν z) (ν 0) n
  have hφ'c : ContinuousOn φ' (Metric.ball 0 ρ₀) :=
    ((hφ.continuousOn.sub continuousOn_const).sub
      (Complex.continuous_re.comp hqd.continuous).continuousOn)
  have hν'c : ContinuousOn ν' (Metric.ball 0 ρ₀) := hνc.div_const _
  have hφ'b : ∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀,
      φ' z ≤ ∑ j, (fun _ => max K₂ 0 / 2) j * ‖z j‖ ^ 2 + C * ‖z‖ ^ 3 := by
    intro z hz
    have h1 := (abs_le.1 (hqb z hz)).2
    have h2 := morseGen_levi_le (fderiv ℝ (fderiv ℝ φ) 0) z
    have h3 := morseGen_sq_le_sum z
    have h4 : ‖fderiv ℝ (fderiv ℝ φ) 0‖ ≤ max K₂ 0 := hK₂.trans (le_max_left _ _)
    have h5 : K₃ ≤ C := (le_max_left _ _).trans (le_add_of_nonneg_right (by positivity))
    have hz3 : 0 ≤ ‖z‖ ^ 3 := by positivity
    have hz2 : 0 ≤ ‖z‖ ^ 2 := by positivity
    rw [← Finset.mul_sum]
    have h6 : ‖fderiv ℝ (fderiv ℝ φ) 0‖ / 2 * ‖z‖ ^ 2 ≤ max K₂ 0 / 2 * ∑ j, ‖z j‖ ^ 2 :=
      mul_le_mul (by linarith) h3 hz2 (by positivity)
    have h7 : K₃ * ‖z‖ ^ 3 ≤ C * ‖z‖ ^ 3 := mul_le_mul_of_nonneg_right h5 hz3
    simp only [hφ']
    linarith
  have hν'b : ∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, 1 - C * ‖z‖ ≤ ν' z := by
    intro z hz
    simp only [hν']
    rw [le_div_iff₀ hν0]
    have h1 := hνL z hz
    have h2 : Lν ≤ C * ν 0 := by
      have : |Lν| / νmin * ν 0 ≥ |Lν| := by
        rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hνmin]
        exact mul_le_mul_of_nonneg_left hνm (abs_nonneg _)
      have : max K₃ 0 * ν 0 ≥ 0 := by positivity
      nlinarith [le_abs_self Lν]
    nlinarith [norm_nonneg z]
  have hν'pos : ∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, 0 ≤ ν' z :=
    fun z hz => div_nonneg (hνpos z hz) hν0.le
  have hexpd : Differentiable ℂ (fun z => cexp (-(n : ℂ) * q z / 2)) := by fun_prop
  have hf'd : DifferentiableOn ℂ f' (Metric.ball 0 ρ₀) := hf.mul hexpd.differentiableOn
  have hint' : IntegrableOn (fun z => ‖f' z‖ ^ 2 * Real.exp (-((n : ℝ) * φ' z)) * ν' z)
      (Metric.ball (0 : Fin D → ℂ) ρ₀) := by
    rw [hfun]; exact hint.mul_const c
  have key := hM n hn (fun _ => max K₂ 0 / 2) φ' ν' f' (fun j => ⟨by positivity, le_rfl⟩)
    hφ'c hν'c hφ'b hν'b hν'pos hf'd hint'
  rw [hfun, integral_mul_const] at key
  have hf0 : f' 0 = f 0 := by simp [hf', hq0]
  rw [hf0] at key
  have hI : 0 ≤ ∫ z in Metric.ball (0 : Fin D → ℂ) ρ₀, g z :=
    setIntegral_nonneg Metric.isOpen_ball.measurableSet fun z hz => by
      simp only [hg]; have := hνpos z hz; positivity
  have hn0 : (0 : ℝ) ≤ (n : ℝ) ^ D := by positivity
  have he : Real.exp (-((n : ℝ) * φ 0)) * Real.exp ((n : ℝ) * φ 0) = 1 := by
    rw [← Real.exp_add]; simp
  have hepos : 0 < Real.exp (-((n : ℝ) * φ 0)) := Real.exp_pos _
  calc ‖f 0‖ ^ 2 * Real.exp (-((n : ℝ) * φ 0))
      ≤ M₀ * (n : ℝ) ^ D * ((∫ z in Metric.ball (0 : Fin D → ℂ) ρ₀, g z) * c) *
          Real.exp (-((n : ℝ) * φ 0)) := mul_le_mul_of_nonneg_right key hepos.le
    _ = M₀ * (n : ℝ) ^ D * (∫ z in Metric.ball (0 : Fin D → ℂ) ρ₀, g z) / ν 0 := by
        rw [hc, div_eq_mul_inv, div_eq_mul_inv]
        linear_combination (M₀ * (n : ℝ) ^ D * (∫ z in Metric.ball (0 : Fin D → ℂ) ρ₀, g z) * (ν 0)⁻¹) * he
    _ ≤ M₀ * (n : ℝ) ^ D * (∫ z in Metric.ball (0 : Fin D → ℂ) ρ₀, g z) / νmin :=
        div_le_div_of_nonneg_left (by positivity) hνmin hνm
    _ = M₀ / νmin * (n : ℝ) ^ D * ∫ z in Metric.ball (0 : Fin D → ℂ) ρ₀, g z := by ring
end ReciprocityTheory.GeometryOfNumbersTheory

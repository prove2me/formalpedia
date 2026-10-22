-- Prove2me | solution 1 for RobbinsMonroSA.Conv.dSeq_nonneg_eSeq_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:15:47.226979+00:00
-- url     : https://prove2.me/submissions/15c7b4fa-3511-40b8-9d06-bb16cef80f37

import Mathlib
import Definitions.Def_RobbinsMonroSA_Conv_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology RobbinsMonroSA.Conv

namespace RMAux

lemma ae_Hresp (H : Kernel ℝ ℝ) [IsMarkovKernel H] (C : ℝ) (h4 : BoundedResponse H C) (z : ℝ) :
    ∀ᵐ y ∂(H z), |y| ≤ C := by
  have h := (prob_compl_eq_zero_iff (μ := H z) (measurableSet_Icc (a := -C) (b := C))).2 (h4.2 z)
  rw [ae_iff]
  refine measure_mono_null ?_ h
  intro y hy
  simpa [abs_le, Set.mem_Icc] using hy

lemma ae_resp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : Kernel ℝ ℝ) [IsMarkovKernel H] (C : ℝ) (h4 : BoundedResponse H C) (α : ℝ)
    (a : ℕ → ℝ) (x1 : ℝ) (x y : ℕ → Ω → ℝ) (hxy : IsRMProcess P H a α x1 x y) (n : ℕ) :
    ∀ᵐ ω ∂P, |y n ω| ≤ C := by
  have hB : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Set.Icc (-C) C} := measurable_snd measurableSet_Icc
  have hmeas : Measurable (fun ω => (x n ω, y n ω)) :=
    (hxy.measurable_x n).prodMk (hxy.measurable_y n)
  have hμ : P.map (fun ω => (x n ω, y n ω)) {p : ℝ × ℝ | p.2 ∈ Set.Icc (-C) C}ᶜ = 0 := by
    rw [hxy.law n, Measure.compProd_apply hB.compl]
    have : ∀ z : ℝ, H z (Prod.mk z ⁻¹' {p : ℝ × ℝ | p.2 ∈ Set.Icc (-C) C}ᶜ) = 0 := by
      intro z
      have e : Prod.mk z ⁻¹' {p : ℝ × ℝ | p.2 ∈ Set.Icc (-C) C}ᶜ = (Set.Icc (-C) C)ᶜ := by
        ext; simp
      rw [e]; exact (prob_compl_eq_zero_iff measurableSet_Icc).2 (h4.2 z)
    exact (lintegral_congr this).trans lintegral_zero
  have h0 : P {ω | (x n ω, y n ω) ∈ {p : ℝ × ℝ | p.2 ∈ Set.Icc (-C) C}ᶜ} = 0 := by
    have hm := Measure.map_apply (μ := P) hmeas hB.compl
    rw [hμ] at hm
    exact hm.symm
  rw [ae_iff]
  refine measure_mono_null ?_ h0
  intro ω hω
  simpa [abs_le, Set.mem_Icc] using hω

lemma M_bound (H : Kernel ℝ ℝ) [IsMarkovKernel H] (C : ℝ) (h4 : BoundedResponse H C) (z : ℝ) :
    |regressionFn H z| ≤ C := by
  unfold regressionFn
  have := norm_integral_le_of_norm_le_const (μ := H z) (f := fun y : ℝ => y) (C := C)
    (by filter_upwards [ae_Hresp H C h4 z] with y hy using by simpa using hy)
  simpa using this

lemma M_meas (H : Kernel ℝ ℝ) [IsMarkovKernel H] : Measurable (regressionFn H) := by
  unfold regressionFn
  exact (StronglyMeasurable.integral_kernel (κ := H) (f := fun y : ℝ => y) stronglyMeasurable_id).measurable

lemma eq22 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : Kernel ℝ ℝ) [IsMarkovKernel H] (C : ℝ) (h4 : BoundedResponse H C) (α θ : ℝ)
    (a : ℕ → ℝ) (x1 : ℝ) (x y : ℕ → Ω → ℝ) (hxy : IsRMProcess P H a α x1 x y)
    (hpos : ∀ n, 0 < a n) :
    ∀ n, ∀ᵐ ω ∂P, |x n ω - θ| ≤ bigA x1 θ C α a n := by
  intro n
  induction n with
  | zero => exact Filter.Eventually.of_forall (fun ω => by simp [bigA, hxy.init ω])
  | succ n ih =>
    filter_upwards [ih, ae_resp P H C h4 α a x1 x y hxy n] with ω h1 h2
    have hstep := hxy.step n ω
    have h3 : |x (n + 1) ω - θ| ≤ |x n ω - θ| + a n * (|α| + C) := by
      have e : x (n + 1) ω - θ = (x n ω - θ) + a n * (α - y n ω) := by linarith
      rw [e]
      refine (abs_add_le _ _).trans ?_
      have : |a n * (α - y n ω)| ≤ a n * (|α| + C) := by
        rw [abs_mul, abs_of_pos (hpos n)]
        refine mul_le_mul_of_nonneg_left ?_ (hpos n).le
        exact (abs_sub _ _).trans (by linarith)
      linarith
    have h4' : bigA x1 θ C α a (n + 1) = bigA x1 θ C α a n + (C + |α|) * a n := by
      unfold bigA; rw [Finset.sum_range_succ]; ring
    rw [h4']
    nlinarith

lemma dnonneg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (H : Kernel ℝ ℝ) (α θ : ℝ)
    (x : ℕ → Ω → ℝ) (h5 : CrossesAt (regressionFn H) α θ) (n : ℕ) :
    0 ≤ dSeq P H α θ x n := by
  unfold dSeq
  apply integral_nonneg
  intro ω
  rcases lt_trichotomy (x n ω) θ with h | h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 h.le) (sub_nonpos.2 (h5.1 _ h))
  · simp [h]
  · exact mul_nonneg (sub_nonneg.2 h.le) (sub_nonneg.2 (h5.2 _ h))

end RMAux

open RMAux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : Kernel ℝ ℝ) [IsMarkovKernel H] (C : ℝ) (h4 : BoundedResponse H C) (α θ : ℝ)
    (a : ℕ → ℝ) (x1 : ℝ) (x y : ℕ → Ω → ℝ) (hxy : IsRMProcess P H a α x1 x y)
    (h5 : CrossesAt (regressionFn H) α θ) :
    ∀ n, 0 ≤ dSeq P H α θ x n ∧ 0 ≤ eSeq P H α x n ∧ eSeq P H α x n ≤ (C + |α|) ^ 2 := by
  intro n
  refine ⟨dnonneg P H α θ x h5 n, ?_, ?_⟩
  · unfold eSeq
    exact integral_nonneg (fun ω => integral_nonneg (fun y => sq_nonneg _))
  · unfold eSeq
    have hb : ∀ z, ∫ y, (y - α) ^ 2 ∂(H z) ≤ (C + |α|) ^ 2 := by
      intro z
      calc ∫ y, (y - α) ^ 2 ∂(H z) ≤ ∫ y, (C + |α|) ^ 2 ∂(H z) := by
            refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => sq_nonneg _))
              (integrable_const _) ?_
            filter_upwards [ae_Hresp H C h4 z] with y hy
            obtain ⟨hy1, hy2⟩ := abs_le.1 hy
            apply sq_le_sq'
            · linarith [neg_abs_le α, le_abs_self α]
            · linarith [le_abs_self α, neg_le_abs α]
        _ = (C + |α|) ^ 2 := by simp
    calc ∫ ω, ∫ y, (y - α) ^ 2 ∂(H (x n ω)) ∂P ≤ ∫ ω, (C + |α|) ^ 2 ∂P := by
          refine integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun ω => integral_nonneg (fun y => sq_nonneg _)))
            (integrable_const _) (Filter.Eventually.of_forall (fun ω => hb _))
      _ = (C + |α|) ^ 2 := by simp

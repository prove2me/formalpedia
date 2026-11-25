-- Prove2me | solution 1 for PI.AprimeInfW.img_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:19:28.974537+00:00
-- url     : https://prove2.me/submissions/601f4831-9bb5-4f74-97ad-e80de8d51fc8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ImgLim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfW
open MeasureTheory Topology Filter
namespace PI.AprimeInfW
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → E} {f' : E → (E →L[ℝ] E)} {U : Set E} {x₀ : E}
    (hf' : ∀ x ∈ U, HasFDerivWithinAt f (f' x) U x) (hinj : Set.InjOn f U)
    (hc : ContinuousAt (fun x => |(f' x).det|) x₀)
    (A : ℕ → Set E) (hAm : ∀ n, MeasurableSet (A n)) (hAU : ∀ n, A n ⊆ U) (hA0 : ∀ n, 0 < μ (A n))
    (hAt : ∀ n, μ (A n) < ⊤) (hsh : ∀ V ∈ 𝓝 x₀, ∀ᶠ n in atTop, A n ⊆ V) :
    Tendsto (fun n => (μ (f '' A n)).toReal / (μ (A n)).toReal) atTop (𝓝 |(f' x₀).det|) := by
  have key : ∀ n, μ (f '' A n) = ∫⁻ x in A n, ENNReal.ofReal |(f' x).det| ∂μ := fun n =>
    (lintegral_abs_det_fderiv_eq_addHaar_image μ (hAm n)
      (fun x hx => (hf' x (hAU n hx)).mono (hAU n)) (hinj.mono (hAU n))).symm
  rw [Metric.tendsto_nhds]
  intro ε hε
  set d := |(f' x₀).det| with hd
  have hV : (fun x => |(f' x).det|) ⁻¹' Set.Ioo (d - ε / 2) (d + ε / 2) ∈ 𝓝 x₀ :=
    hc (Ioo_mem_nhds (by linarith) (by linarith))
  filter_upwards [hsh _ hV] with n hn
  have hm0 := hA0 n
  have hmt := hAt n
  have hmr : 0 < (μ (A n)).toReal := ENNReal.toReal_pos hm0.ne' hmt.ne
  have up : ∫⁻ x in A n, ENNReal.ofReal |(f' x).det| ∂μ ≤ ENNReal.ofReal (d + ε / 2) * μ (A n) := by
    calc _ ≤ ∫⁻ _ in A n, ENNReal.ofReal (d + ε / 2) ∂μ :=
          lintegral_mono_ae ((ae_restrict_iff' (hAm n)).2 (Eventually.of_forall fun x hx =>
            ENNReal.ofReal_le_ofReal (hn hx).2.le))
      _ = _ := setLIntegral_const _ _
  have lo : ENNReal.ofReal (d - ε / 2) * μ (A n) ≤ ∫⁻ x in A n, ENNReal.ofReal |(f' x).det| ∂μ := by
    calc _ = ∫⁻ _ in A n, ENNReal.ofReal (d - ε / 2) ∂μ := (setLIntegral_const _ _).symm
      _ ≤ _ := lintegral_mono_ae ((ae_restrict_iff' (hAm n)).2 (Eventually.of_forall fun x hx =>
            ENNReal.ofReal_le_ofReal (hn hx).1.le))
  have hupt : ENNReal.ofReal (d + ε / 2) * μ (A n) ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmt.ne
  have hIt : ∫⁻ x in A n, ENNReal.ofReal |(f' x).det| ∂μ ≠ ⊤ := ne_top_of_le_ne_top hupt up
  have u1 : (∫⁻ x in A n, ENNReal.ofReal |(f' x).det| ∂μ).toReal ≤ (d + ε / 2) * (μ (A n)).toReal := by
    have := ENNReal.toReal_mono hupt up
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have l1 : (d - ε / 2) * (μ (A n)).toReal ≤ (∫⁻ x in A n, ENNReal.ofReal |(f' x).det| ∂μ).toReal := by
    have := ENNReal.toReal_mono hIt lo
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal'] at this
    exact le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hmr.le) this
  rw [key n, Real.dist_eq, abs_sub_lt_iff]
  constructor
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hmr]; nlinarith
  · rw [sub_lt_comm, lt_div_iff₀ hmr]; nlinarith
end PI.AprimeInfW

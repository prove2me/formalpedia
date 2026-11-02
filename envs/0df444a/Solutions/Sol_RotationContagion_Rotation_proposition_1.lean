-- Prove2me | solution 1 for RotationContagion.Rotation.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T09:58:15.177224+00:00
-- url     : https://prove2.me/submissions/55ce49cb-ca9a-4464-9737-b7b486f75719

import Mathlib
import Definitions.Def_RotationContagion_Rotation_Model
import Theorems.Thm_RotationContagion_Rotation_lemma_1
import Theorems.Thm_RotationContagion_Rotation_lemma_3

open MeasureTheory Set Filter

namespace RotContProp1

open RotationContagion.Rotation

lemma ii_of_bdd (g : ℝ → ℝ) (hg : Measurable g) (hb : ∀ s, g s ∈ Icc (0:ℝ) 1) (a c : ℝ) :
    IntervalIntegrable g volume a c := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := 1) ?_ hg.aestronglyMeasurable ?_
  · exact ((measure_mono Set.uIoc_subset_uIcc).trans_lt isCompact_uIcc.measure_lt_top).ne
  · exact Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hb s).1, (hb s).2]

lemma loss_bdd (P : Params) (x : ℝ) : |loss P x| ≤ 1 := by
  unfold loss
  have h := Real.exp_pos (P.γ * (x - b P))
  rw [abs_le]
  constructor
  · have : 0 ≤ Real.exp (P.γ * (x - b P)) / (1 + Real.exp (P.γ * (x - b P))) := by positivity
    linarith
  · rw [div_le_one (by linarith)]; linarith

lemma exp_sum (P : Params) (r : Fin 2 → ℝ → ℝ) (hr : IsSchedule r) (t0 : ℝ) :
    exposure P r 0 t0 + exposure P r 1 t0 = P.R := by
  unfold exposure
  rw [← intervalIntegral.integral_add (ii_of_bdd _ (hr.1 0) (fun s => (hr.2 s).1 0) _ _)
    (ii_of_bdd _ (hr.1 1) (fun s => (hr.2 s).1 1) _ _)]
  have : ∀ s, r 0 s + r 1 s = 1 := fun s => (hr.2 s).2
  simp only [this, intervalIntegral.integral_const, smul_eq_mul, mul_one]
  ring

lemma exp_mem (P : Params) (hP : P.Standing) (r : Fin 2 → ℝ → ℝ) (hr : IsSchedule r)
    (ω : Fin 2) (t0 : ℝ) : exposure P r ω t0 ∈ Icc 0 P.R := by
  have hR := hP.2.2
  have hle : t0 ≤ t0 + P.R := by linarith
  have hii := ii_of_bdd _ (hr.1 ω) (fun s => (hr.2 s).1 ω)
  unfold exposure
  constructor
  · exact intervalIntegral.integral_nonneg hle (fun s _ => ((hr.2 s).1 ω).1)
  · have := intervalIntegral.integral_mono_on hle (hii _ _) intervalIntegrable_const
      (fun s _ => ((hr.2 s).1 ω).2)
    simpa using this

lemma exp_cont (P : Params) (r : Fin 2 → ℝ → ℝ) (hr : IsSchedule r) (ω : Fin 2) :
    Continuous (fun t0 => exposure P r ω t0) := by
  have hii := ii_of_bdd _ (hr.1 ω) (fun s => (hr.2 s).1 ω)
  have hF := intervalIntegral.continuous_primitive hii 0
  have : (fun t0 => exposure P r ω t0) =
      fun t0 => (∫ s in (0:ℝ)..t0 + P.R, r ω s) - ∫ s in (0:ℝ)..t0, r ω s := by
    funext t0
    unfold exposure
    rw [intervalIntegral.integral_interval_sub_left (hii _ _) (hii _ _)]
  rw [this]
  exact (hF.comp (continuous_id.add continuous_const)).sub hF

lemma int_loss (P : Params) (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hf : Continuous f) (hc : Continuous (loss P)) :
    Integrable (fun t0 => loss P (f t0)) μ :=
  Integrable.of_bound (hc.comp hf).aestronglyMeasurable 1
    (Eventually.of_forall fun t0 => by rw [Real.norm_eq_abs]; exact loss_bdd P _)

lemma ET_eq (P : Params) (hP : P.Standing) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) (r : Fin 2 → ℝ → ℝ) (hr : IsSchedule r)
    (p : Fin 2 → ℝ → ℝ → ℝ) (hp : IsPrevalenceFamily P r p) (hc : Continuous (loss P)) :
    expectedTerminal P μ p = (1 / 2) * ∫ t0, relaxedObj P (exposure P r 0 t0) ∂μ := by
  have hae : ∀ᵐ t0 ∂μ, 0 ≤ t0 := by
    rw [ae_iff]
    have : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext a; simp
    rw [this]; exact hμ
  have hterm : ∀ ω t0, 0 ≤ t0 → p ω t0 (t0 + P.R) = loss P (exposure P r ω t0) :=
    fun ω t0 ht0 => ((lemma_1 P hP r hr ω t0 ht0).2 _ (hp ω t0 ht0)).2
  unfold expectedTerminal
  rw [Fin.sum_univ_two]
  have h0 : ∫ t0, p 0 t0 (t0 + P.R) ∂μ = ∫ t0, loss P (exposure P r 0 t0) ∂μ :=
    integral_congr_ae (by filter_upwards [hae] with t0 ht0 using hterm 0 t0 ht0)
  have h1 : ∫ t0, p 1 t0 (t0 + P.R) ∂μ = ∫ t0, loss P (P.R - exposure P r 0 t0) ∂μ :=
    integral_congr_ae (by
      filter_upwards [hae] with t0 ht0
      rw [hterm 1 t0 ht0]
      congr 1
      linarith [exp_sum P r hr t0])
  rw [h0, h1, ← integral_add (int_loss P μ _ (exp_cont P r hr 0) hc)
    (int_loss P μ (fun t0 => P.R - exposure P r 0 t0) (continuous_const.sub (exp_cont P r hr 0)) hc)]
  rfl

lemma opt_of_const (P : Params) (hP : P.Standing) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) (r : Fin 2 → ℝ → ℝ) (hr : IsSchedule r) (c : ℝ)
    (hconst : ∀ t0, exposure P r 0 t0 = c)
    (hmin : ∀ τ ∈ Icc 0 P.R, relaxedObj P c ≤ relaxedObj P τ) : IsOptimal P μ r := by
  have hc : Continuous (loss P) := by
    unfold loss
    have : ∀ x, 1 + Real.exp (P.γ * (x - b P)) ≠ 0 := fun x => by positivity
    fun_prop (disch := exact this _)
  refine ⟨hr, ⟨fun ω t0 t => loss P (∫ s in t0..t, r ω s),
    fun ω t0 ht0 => (lemma_1 P hP r hr ω t0 ht0).1⟩, ?_⟩
  intro p hp r' p' hr' hp'
  rw [ET_eq P hP μ hμ r hr p hp hc, ET_eq P hP μ hμ r' hr' p' hp' hc]
  simp only [hconst]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hint : Integrable (fun t0 => relaxedObj P (exposure P r' 0 t0)) μ := by
    unfold relaxedObj
    exact (int_loss P μ _ (exp_cont P r' hr' 0) hc).add
      (int_loss P μ (fun t0 => P.R - exposure P r' 0 t0) (continuous_const.sub (exp_cont P r' hr' 0)) hc)
  calc ∫ _t0, relaxedObj P c ∂μ ≤ ∫ t0, relaxedObj P (exposure P r' 0 t0) ∂μ :=
        integral_mono (integrable_const _) hint (fun t0 => hmin _ (exp_mem P hP r' hr' 0 t0))
    _ = _ := rfl

end RotContProp1

open RotationContagion.Rotation RotContProp1 in
theorem solution (P : Params) (hP : P.Standing) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) :
    (P.R / 2 < b P → IsOptimal P μ freqSched) ∧
      (b P < P.R / 2 → ∀ i : Fin 2, IsOptimal P μ (oneGroupSched i)) := by
  have hR := hP.2.2
  obtain ⟨h3a, h3b⟩ := lemma_3 P hP
  constructor
  · intro hlt
    obtain ⟨hanti, hmono⟩ := h3a hlt
    have hsched : IsSchedule freqSched := by
      refine ⟨fun i => measurable_const, fun t => ⟨fun i => ?_, ?_⟩⟩
      · simp only [freqSched]; constructor <;> norm_num
      · simp only [freqSched]; norm_num
    refine opt_of_const P hP μ hμ freqSched hsched (P.R / 2) (fun t0 => ?_) (fun τ _ => ?_)
    · unfold exposure freqSched
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring
    · rcases le_total τ (P.R / 2) with h | h
      · exact hanti.antitoneOn (show τ ∈ Iic (P.R / 2) from h)
          (Set.mem_Iic.2 le_rfl) h
      · exact hmono.monotoneOn (Set.mem_Ici.2 le_rfl)
          (show τ ∈ Ici (P.R / 2) from h) h
  · intro hlt i
    obtain ⟨hmono, hanti⟩ := h3b hlt
    have hsym : relaxedObj P P.R = relaxedObj P 0 := by
      unfold relaxedObj; simp only [sub_self, sub_zero]; ring
    have hsched : IsSchedule (oneGroupSched i) := by
      refine ⟨fun j => measurable_const, fun t => ⟨fun j => ?_, ?_⟩⟩
      · simp only [oneGroupSched]; split_ifs <;> norm_num
      · fin_cases i <;> simp [oneGroupSched]
    have hmin : ∀ τ ∈ Icc 0 P.R, relaxedObj P 0 ≤ relaxedObj P τ := by
      intro τ hτ
      rcases le_total τ (P.R / 2) with h | h
      · exact hmono.monotoneOn (show (0:ℝ) ∈ Iic (P.R / 2) by simp only [mem_Iic]; linarith)
          (show τ ∈ Iic (P.R / 2) from h) hτ.1
      · rw [← hsym]
        exact hanti.antitoneOn (show τ ∈ Ici (P.R / 2) from h)
          (show P.R ∈ Ici (P.R / 2) by simp only [mem_Ici]; linarith) hτ.2
    fin_cases i
    · refine opt_of_const P hP μ hμ _ hsched P.R (fun t0 => ?_) ?_
      · unfold exposure oneGroupSched
        simp
      · intro τ hτ; rw [hsym]; exact hmin τ hτ
    · refine opt_of_const P hP μ hμ _ hsched 0 (fun t0 => ?_) hmin
      unfold exposure oneGroupSched
      simp

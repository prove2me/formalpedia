-- Prove2me | solution 1 for StochasticOrders.MeanResidualLife.dmrl_mrl_order_add_indep
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T09:10:24.066755+00:00
-- url     : https://prove2.me/submissions/adf16b06-3dfc-416f-a27b-918136f41c6f

import Mathlib
import Definitions.Def_StochasticOrders_MeanResidualLife_mrl
import Definitions.Def_StochasticOrders_MeanResidualLife_MrlOrder
import Definitions.Def_StochasticOrders_MeanResidualLife_DMRL

set_option autoImplicit false

namespace P9d53c85c

open MeasureTheory ProbabilityTheory StochasticOrders.MeanResidualLife

/-- excess over `s`: `(x - s) 1{x > s}` -/
noncomputable def phi (s : ℝ) (x : ℝ) : ℝ := Set.indicator (Set.Ioi s) (fun x => x - s) x

/-- tail indicator `1{x > s}` -/
noncomputable def psi (s : ℝ) (x : ℝ) : ℝ := Set.indicator (Set.Ioi s) (fun _ => (1 : ℝ)) x

lemma phi_measurable (s : ℝ) : Measurable (phi s) :=
  (measurable_id.sub measurable_const).indicator measurableSet_Ioi

lemma psi_measurable (s : ℝ) : Measurable (psi s) :=
  measurable_const.indicator measurableSet_Ioi

lemma phi_comp {Ω : Type*} [MeasurableSpace Ω] (Y : Ω → ℝ) (s : ℝ) :
    (fun ω => phi s (Y ω)) = Set.indicator {ω | s < Y ω} (fun ω => Y ω - s) := by
  ext ω; simp [phi, Set.indicator]

lemma psi_comp {Ω : Type*} [MeasurableSpace Ω] (Y : Ω → ℝ) (s : ℝ) :
    (fun ω => psi s (Y ω)) = Set.indicator {ω | s < Y ω} (fun _ => (1 : ℝ)) := by
  ext ω; simp [psi, Set.indicator]

lemma phi_int {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : Measurable Y) (hYi : Integrable Y μ) (s : ℝ) :
    Integrable (fun ω => phi s (Y ω)) μ := by
  rw [phi_comp]
  exact (hYi.sub (integrable_const s)).indicator (measurableSet_lt measurable_const hY)

lemma psi_int {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : Measurable Y) (s : ℝ) :
    Integrable (fun ω => psi s (Y ω)) μ := by
  rw [psi_comp]
  exact (integrable_const (1 : ℝ)).indicator (measurableSet_lt measurable_const hY)

lemma setInt_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → ℝ) (hY : Measurable Y) (s : ℝ) :
    ∫ ω in {ω | s < Y ω}, (Y ω - s) ∂μ = ∫ ω, phi s (Y ω) ∂μ := by
  rw [phi_comp, integral_indicator (measurableSet_lt measurable_const hY)]

lemma psi_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : Measurable Y) (s : ℝ) :
    ∫ ω, psi s (Y ω) ∂μ = (μ {ω | s < Y ω}).toReal := by
  rw [psi_comp, integral_indicator (measurableSet_lt measurable_const hY)]
  simp [Measure.real]

lemma mrl_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : Measurable Y) (s : ℝ) (h : 0 < (μ {ω | s < Y ω}).toReal) :
    mrl μ Y s = (∫ ω, phi s (Y ω) ∂μ) / ∫ ω, psi s (Y ω) ∂μ := by
  unfold mrl
  rw [if_pos h, setInt_eq μ Y hY s, psi_integral μ Y hY s]

lemma key {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (hD : DMRL μ X) (t s : ℝ) (hst : s ≤ t)
    (hpos : 0 < (μ {ω | t < X ω}).toReal) :
    mrl μ X t * ∫ ω, psi s (X ω) ∂μ ≤ ∫ ω, phi s (X ω) ∂μ := by
  have hmono : (μ {ω | t < X ω}).toReal ≤ (μ {ω | s < X ω}).toReal := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    linarith
  have hps : 0 < (μ {ω | s < X ω}).toReal := lt_of_lt_of_le hpos hmono
  have hm : mrl μ X t ≤ mrl μ X s := hD hst
  rw [mrl_eq μ X hX s hps] at hm
  have hP : 0 < ∫ ω, psi s (X ω) ∂μ := by rw [psi_integral μ X hX s]; exact hps
  rwa [le_div_iff₀ hP] at hm

lemma main_ineq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z)
    (hXi : Integrable X μ) (hZi : Integrable Z μ)
    (hDMRL : DMRL μ X) (hZnn : ∀ ω, 0 ≤ Z ω) (hindep : IndepFun X Z μ) (t : ℝ)
    (hpos : 0 < (μ {ω | t < X ω}).toReal) :
    mrl μ X t * ∫ ω, psi t (X ω + Z ω) ∂μ ≤ ∫ ω, phi t (X ω + Z ω) ∂μ := by
  set c := mrl μ X t with hc
  let F : ℝ × ℝ → ℝ := fun p => phi t (p.1 + p.2) - c * psi t (p.1 + p.2)
  have hFm : Measurable F :=
    ((phi_measurable t).comp (measurable_fst.add measurable_snd)).sub
      (measurable_const.mul ((psi_measurable t).comp (measurable_fst.add measurable_snd)))
  have hXZ : Measurable (fun ω => (X ω, Z ω)) := hX.prodMk hZ
  have hYm : Measurable (fun ω => X ω + Z ω) := hX.add hZ
  have hYi : Integrable (fun ω => X ω + Z ω) μ := hXi.add hZi
  have hcomp : Integrable (fun ω => F (X ω, Z ω)) μ :=
    (phi_int μ _ hYm hYi t).sub ((psi_int μ _ hYm t).const_mul c)
  have : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have : IsProbabilityMeasure (μ.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  have hmap : μ.map (fun ω => (X ω, Z ω)) = (μ.map X).prod (μ.map Z) :=
    (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hZ.aemeasurable).1 hindep
  have hFint : Integrable F ((μ.map X).prod (μ.map Z)) := by
    rw [← hmap]
    exact (integrable_map_measure hFm.aestronglyMeasurable hXZ.aemeasurable).2 hcomp
  have h1 : ∫ ω, F (X ω, Z ω) ∂μ = ∫ z, ∫ x, F (x, z) ∂(μ.map X) ∂(μ.map Z) := by
    rw [← integral_prod_symm F hFint, ← hmap,
      integral_map hXZ.aemeasurable hFm.aestronglyMeasurable]
  have h2 : 0 ≤ ∫ ω, F (X ω, Z ω) ∂μ := by
    rw [h1]
    apply integral_nonneg_of_ae
    have hae : ∀ᵐ z ∂(μ.map Z), 0 ≤ z :=
      (ae_map_iff hZ.aemeasurable (measurableSet_le measurable_const measurable_id)).2
        (ae_of_all _ hZnn)
    filter_upwards [hae] with z hz
    have hFz : Measurable (fun x : ℝ => F (x, z)) := hFm.comp (measurable_id.prodMk measurable_const)
    rw [integral_map hX.aemeasurable hFz.aestronglyMeasurable]
    have hpt : (fun ω => F (X ω, z)) =
        fun ω => phi (t - z) (X ω) - c * psi (t - z) (X ω) := by
      ext ω
      simp only [F, phi, psi, Set.indicator, Set.mem_Ioi]
      have e : (t < X ω + z) ↔ (t - z < X ω) := by constructor <;> intro h <;> linarith
      by_cases h : t - z < X ω
      · have h' := e.2 h
        simp only [if_pos h, if_pos h']
        ring
      · have h' : ¬ t < X ω + z := fun h' => h (e.1 h')
        simp only [if_neg h, if_neg h']
    rw [hpt, integral_sub (phi_int μ X hX hXi _) ((psi_int μ X hX _).const_mul c),
      integral_const_mul]
    have := key μ X hX hDMRL t (t - z) (by linarith) hpos
    rw [← hc] at this
    simp only [Pi.zero_apply]
    linarith
  have h3 : ∫ ω, F (X ω, Z ω) ∂μ =
      ∫ ω, phi t (X ω + Z ω) ∂μ - c * ∫ ω, psi t (X ω + Z ω) ∂μ := by
    simp only [F]
    rw [integral_sub (phi_int μ _ hYm hYi t) ((psi_int μ _ hYm t).const_mul c),
      integral_const_mul]
  linarith

end P9d53c85c

open MeasureTheory ProbabilityTheory StochasticOrders.MeanResidualLife in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z)
    (hXi : Integrable X μ) (hZi : Integrable Z μ)
    (hDMRL : DMRL μ X) (hZnn : ∀ ω, 0 ≤ Z ω) (hindep : IndepFun X Z μ) :
    MrlOrder μ μ X (fun ω => X ω + Z ω) := by
  intro t
  have hYm : Measurable (fun ω => X ω + Z ω) := hX.add hZ
  by_cases hpos : 0 < (μ {ω | t < X ω}).toReal
  · have hmono : (μ {ω | t < X ω}).toReal ≤ (μ {ω | t < X ω + Z ω}).toReal := by
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      linarith [hZnn ω]
    have hpos' : 0 < (μ {ω | t < X ω + Z ω}).toReal := lt_of_lt_of_le hpos hmono
    rw [P9d53c85c.mrl_eq μ _ hYm t hpos']
    have hP : 0 < ∫ ω, P9d53c85c.psi t (X ω + Z ω) ∂μ := by
      rw [P9d53c85c.psi_integral μ _ hYm t]; exact hpos'
    rw [le_div_iff₀ hP]
    exact P9d53c85c.main_ineq μ X Z hX hZ hXi hZi hDMRL hZnn hindep t hpos
  · have h0 : mrl μ X t = 0 := by
      unfold mrl; rw [if_neg hpos]
    rw [h0]
    unfold mrl
    split_ifs with h
    · apply div_nonneg _ ENNReal.toReal_nonneg
      apply setIntegral_nonneg (measurableSet_lt measurable_const hYm)
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω
      linarith
    · exact le_refl _

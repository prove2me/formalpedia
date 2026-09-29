-- Prove2me | solution 1 for StickyKakeya4.selector_closure
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @sensei
-- created : 2026-09-27T12:44:51.826325+00:00
-- url     : https://prove2.me/submissions/faea117e-c987-4a46-aaa2-e52bbcd98e8c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StickyKakeya4_packing_selector_to_finite_scale_sources
import Theorems.Thm_StickyKakeya4_uniform_marked_source_hereditary_finite_scale
import Theorems.Thm_StickyKakeya4_hereditary_finite_scale_to_frostman

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace StickyKakeya4

private theorem singleton_zero_of_growth
    (mu : Measure E4) (C : ENNReal) (hCtop : C ≠ ⊤)
    (d : ℝ) (hd : 0 < d)
    (hball : ∀ (x : E4) (r : ℝ), 0 < r → r ≤ 1 →
      mu (Metric.ball x r) ≤ C * (ENNReal.ofReal r).rpow d)
    (x : E4) : mu {x} = 0 := by
  apply bot_unique
  have hlim : Tendsto (fun r : ENNReal => C * r.rpow d)
      (𝓝[>] (0 : ENNReal)) (𝓝 0) :=
    (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hCtop hd).mono_left
      inf_le_left
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin,
      (eventually_le_nhds (show (0 : ENNReal) < 1 by norm_num)).filter_mono
        inf_le_left] with r hrpos hrle
  have hr0 : r ≠ 0 := ne_of_gt hrpos
  have hrtop : r ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hrle
  have hrRealPos : 0 < r.toReal := ENNReal.toReal_pos hr0 hrtop
  have hrRealLe : r.toReal ≤ 1 := by
    simpa using (ENNReal.toReal_le_toReal hrtop ENNReal.one_ne_top).2 hrle
  have hsingleton : {x} ⊆ Metric.ball x r.toReal := by
    intro y hy
    rcases hy with rfl
    simpa [Metric.mem_ball] using hrRealPos
  calc
    mu {x} ≤ mu (Metric.ball x r.toReal) := measure_mono hsingleton
    _ ≤ C * (ENNReal.ofReal r.toReal).rpow d :=
      hball x r.toReal hrRealPos hrRealLe
    _ = C * r.rpow d := by rw [ENNReal.ofReal_toReal hrtop]

private theorem measure_le_diameter_power_of_growth
    (mu : Measure E4) (C : ENNReal) (hCtop : C ≠ ⊤)
    (d : ℝ) (hd : 0 < d)
    (hball : ∀ (x : E4) (r : ℝ), 0 < r → r ≤ 1 →
      mu (Metric.ball x r) ≤ C * (ENNReal.ofReal r).rpow d)
    (s : Set E4) (hsdiam : Metric.ediam s ≤ (1 / 2 : ENNReal)) :
    mu s ≤ (C * (2 : ENNReal).rpow d) * Metric.ediam s ^ d := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  by_cases hdiam0 : Metric.ediam s = 0
  · have hsubsingle : s.Subsingleton := Metric.ediam_eq_zero_iff.mp hdiam0
    obtain ⟨x, hx⟩ := hs
    have hsx : s = {x} := (subsingleton_iff_singleton hx).mp hsubsingle
    rw [hsx, singleton_zero_of_growth mu C hCtop d hd hball x]
    simp
  · obtain ⟨x, hx⟩ := hs
    have hdiamtop : Metric.ediam s ≠ ⊤ :=
      ne_top_of_le_ne_top (by norm_num : (1 / 2 : ENNReal) ≠ ⊤) hsdiam
    have hdiampos : 0 < (Metric.ediam s).toReal :=
      ENNReal.toReal_pos hdiam0 hdiamtop
    have hsubset : s ⊆ Metric.ball x (2 * (Metric.ediam s).toReal) := by
      intro y hy
      rw [Metric.mem_ball]
      have hdist : dist y x ≤ (Metric.ediam s).toReal := by
        rw [dist_edist]
        exact (ENNReal.toReal_le_toReal (edist_ne_top _ _) hdiamtop).2
          (Metric.edist_le_ediam_of_mem hy hx)
      nlinarith
    have hrpos : 0 < 2 * (Metric.ediam s).toReal := by positivity
    have hrle : 2 * (Metric.ediam s).toReal ≤ 1 := by
      have hdiamRealLe : (Metric.ediam s).toReal ≤ (1 / 2 : ENNReal).toReal :=
        (ENNReal.toReal_le_toReal hdiamtop (by norm_num)).2 hsdiam
      norm_num at hdiamRealLe ⊢
      linarith
    calc
      mu s ≤ mu (Metric.ball x (2 * (Metric.ediam s).toReal)) :=
        measure_mono hsubset
      _ ≤ C * (ENNReal.ofReal (2 * (Metric.ediam s).toReal)).rpow d :=
        hball x (2 * (Metric.ediam s).toReal) hrpos hrle
      _ = (C * (2 : ENNReal).rpow d) * Metric.ediam s ^ d := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 2),
          ENNReal.ofReal_toReal hdiamtop]
        simp only [ENNReal.ofReal_ofNat]
        calc
          C * (2 * Metric.ediam s).rpow d =
              C * ((2 : ENNReal).rpow d * Metric.ediam s ^ d) := by
                change C * ((2 * Metric.ediam s) ^ d) =
                  C * ((2 : ENNReal) ^ d * Metric.ediam s ^ d)
                rw [ENNReal.mul_rpow_of_nonneg _ _ hd.le]
          _ = (C * (2 : ENNReal).rpow d) * Metric.ediam s ^ d := by
            ac_rfl

private theorem hausdorffMeasure_ne_zero_of_growth
    (mu : Measure E4) [IsProbabilityMeasure mu]
    (s : Set E4) (hsupport : mu s.compl = 0)
    (C : ENNReal) (hCtop : C ≠ ⊤)
    (dnn : NNReal) (hdnn : 0 < dnn)
    (hball : ∀ (x : E4) (r : ℝ), 0 < r → r ≤ 1 →
      mu (Metric.ball x r) ≤ C * (ENNReal.ofReal r).rpow (dnn : ℝ)) :
    MeasureTheory.Measure.hausdorffMeasure (dnn : ℝ) s ≠ 0 := by
  let K : ENNReal := max 1 (C * (2 : ENNReal).rpow (dnn : Real))
  have hK0 : K ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1)
      (le_max_left _ _))
  have hKtop : K ≠ ⊤ := by
    apply ne_of_lt
    dsimp [K]
    rw [max_lt_iff]
    constructor
    · exact ENNReal.one_lt_top
    · exact lt_top_iff_ne_top.mpr <|
        ENNReal.mul_ne_top hCtop
          (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by norm_num))
  let nu : Measure E4 := K⁻¹ • mu
  have hnu_le : nu ≤ MeasureTheory.Measure.hausdorffMeasure (dnn : ℝ) := by
    apply MeasureTheory.Measure.le_hausdorffMeasure (dnn : ℝ) nu (1 / 2)
      (by norm_num)
    intro t htdiam
    rw [show nu t = K⁻¹ * mu t by simp [nu]]
    calc
      K⁻¹ * mu t ≤ K⁻¹ *
          ((C * (2 : ENNReal).rpow (dnn : ℝ)) *
            Metric.ediam t ^ (dnn : ℝ)) := by
        gcongr
        exact measure_le_diameter_power_of_growth
          mu C hCtop (dnn : ℝ) (by exact_mod_cast hdnn) hball t htdiam
      _ ≤ K⁻¹ * (K * Metric.ediam t ^ (dnn : ℝ)) := by
        gcongr
        exact le_max_right _ _
      _ = Metric.ediam t ^ (dnn : ℝ) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hK0 hKtop, one_mul]
  have hmus : mu s ≠ 0 := by
    intro hmus0
    have hsunion : mu (s ∪ s.compl) = 0 :=
      measure_union_null hmus0 hsupport
    have hcover : s ∪ s.compl = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      by_cases hx : x ∈ s
      · exact Or.inl hx
      · exact Or.inr hx
    rw [hcover, measure_univ] at hsunion
    exact one_ne_zero hsunion
  have hnus : nu s ≠ 0 := by
    rw [show nu s = K⁻¹ * mu s by simp [nu]]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr hKtop) hmus
  intro hzero
  apply hnus
  apply bot_unique
  simpa [hzero] using hnu_le s

private theorem four_le_dimH_of_front_frostman
    (selector : Set MarkedLine)
    (hfrost : HasFrontFrostmanMeasures selector) :
    (4 : ENNReal) ≤ dimH (unitFront selector) := by
  by_contra hnot
  have hlt : dimH (unitFront selector) < (4 : ENNReal) := lt_of_not_ge hnot
  have hfourltTop : (4 : ENNReal) < ⊤ := by norm_num
  have hdimtop : dimH (unitFront selector) ≠ ⊤ :=
    ne_top_of_lt (hlt.trans hfourltTop)
  have hfourtop : (4 : ENNReal) ≠ ⊤ := by norm_num
  have hdimRealLt : (dimH (unitFront selector)).toReal < 4 :=
    (ENNReal.toReal_lt_toReal hdimtop hfourtop).2 hlt
  let ε : ℝ := (4 - (dimH (unitFront selector)).toReal) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hε4 : ε < 4 := by
    have hdimRealNonneg : 0 ≤ (dimH (unitFront selector)).toReal :=
      ENNReal.toReal_nonneg
    dsimp [ε]
    linarith
  obtain ⟨mu, hmuProb, hsupport, C, hCtop, hball⟩ :=
    hfrost ε hε hε4
  letI : IsProbabilityMeasure mu := hmuProb
  let dnn : NNReal := ⟨4 - ε, le_of_lt (sub_pos.mpr hε4)⟩
  have hdnnReal : (dnn : ℝ) = 4 - ε := by rfl
  have hballD : ∀ (x : E4) (r : ℝ), 0 < r → r ≤ 1 →
      mu (Metric.ball x r) ≤
        C * (ENNReal.ofReal r).rpow (dnn : ℝ) := by
    intro x r hr hr1
    rw [hdnnReal]
    exact hball x r hr hr1
  have hhaus :
      MeasureTheory.Measure.hausdorffMeasure (dnn : ℝ)
        (unitFront selector) ≠ 0 :=
    hausdorffMeasure_ne_zero_of_growth
      mu (unitFront selector) hsupport C hCtop dnn
        (by exact_mod_cast (sub_pos.mpr hε4)) hballD
  have hdimLower : (dnn : ENNReal) ≤ dimH (unitFront selector) :=
    le_dimH_of_hausdorffMeasure_ne_zero hhaus
  have hdimRealLower : (dnn : ENNReal).toReal ≤
      (dimH (unitFront selector)).toReal :=
    (ENNReal.toReal_le_toReal (by simp) hdimtop).2 hdimLower
  have hdnnToReal : (dnn : ENNReal).toReal = 4 - ε := by
    change (dnn : ℝ) = 4 - ε
    exact hdnnReal
  have hmidLower : 4 - ε ≤ (dimH (unitFront selector)).toReal := by
    rw [← hdnnToReal]
    exact hdimRealLower
  dsimp [ε] at hmidLower
  linarith

end StickyKakeya4

open StickyKakeya4

theorem solution (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hpacking : packingDim (lineCarrier selector) = 3) :
    dimH (unitFront selector) = 4 := by
  have hsources : HasCoherentFiniteScaleSources selector :=
    packing_selector_to_finite_scale_sources selector hmeasurable hvalid
      hselector hpacking
  have huniform : HasUniformMarkedSourceEstimate selector :=
    uniform_marked_source_hereditary_finite_scale selector hmeasurable hvalid
      hselector hpacking
  have hfrost : HasFrontFrostmanMeasures selector :=
    hereditary_finite_scale_to_frostman selector hmeasurable hvalid
      hselector hpacking hsources huniform
  apply le_antisymm
  · calc
      dimH (unitFront selector) ≤ dimH (Set.univ : Set E4) :=
        dimH_mono (Set.subset_univ _)
      _ = 4 := by simp [E4, Real.dimH_univ_eq_finrank]
  · exact four_le_dimH_of_front_frostman selector hfrost

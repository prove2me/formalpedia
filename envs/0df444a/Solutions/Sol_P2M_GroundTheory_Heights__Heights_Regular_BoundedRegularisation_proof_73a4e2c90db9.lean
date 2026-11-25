-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_BoundedRegularisation_proof_73a4e2c90db9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:31:16.057806+00:00
-- url     : https://prove2.me/submissions/c7b7d3b2-9478-4227-9636-bfb904ada76f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_BoundedStatements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsCompactImageClosureMid
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_continuous_of_atlasSmooth_9b3e9dc0f791
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_regMax_bounds_7e37d99f8d7b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_exists_margin_d7498302d171
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_exists_bound_q_d6a91a56a3ee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_mid_subset_source_96b409876f03
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshMean_isOpen_inter_preimage
import Theorems.Thm_ReciprocityTheory_AnForm_A_mollifierInhabit_thm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli shrink regMax tmax)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open ReciprocityTheory.AnForm (levi)
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
namespace BoundedRegularisation
theorem _root_.solution (h0 : BoundedChartComparison.Statement)
    (h1 : BoundedGlue.Statement) (h2 : CutoffsExist.Statement)
    (h3 : ReciprocityTheory.AnForm.A.MollifyStatement) : BoundedRegularisation.Statement := by
  classical
  intro X _ _ _ D A B
  obtain ⟨ρ⟩ := ReciprocityTheory.AnForm.A.mollifierInhabit_thm D
  obtain ⟨C₀, t₁, ht₁, hcmp⟩ := h0 X D A B ρ
  obtain ⟨η, Cη, hη⟩ := h2 X D A B.toPotentialCharts
  obtain ⟨δ, hδ, hmarg⟩ := B.toPotentialCharts.exists_margin
  obtain ⟨Q, hQ⟩ := B.toPotentialCharts.exists_bound_q hmarg
  obtain ⟨Cb, hCb⟩ := B.bdd
  set C₁ : ℝ := max C₀ 1 with hC₁
  have hC₁pos : 0 < C₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  set ε : ℝ → ℝ := fun t => C₁ / Real.log t⁻¹ + C₁ * t with hε
  set t₀ : ℝ := min (min t₁ δ) (1 / 2) with ht₀
  have ht₀pos : 0 < t₀ := lt_min (lt_min ht₁ hδ) (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two

  have hℓ : ∀ t, 0 < t → t < t₀ → Real.log 2 ≤ Real.log t⁻¹ := by
    intro t ht htt
    have : t ≤ 1 / 2 := htt.le.trans (min_le_right _ _)
    apply Real.log_le_log two_pos
    rw [le_inv_comm₀ two_pos ht]
    linarith
  have hℓpos : ∀ t, 0 < t → t < t₀ → 0 < Real.log t⁻¹ :=
    fun t ht htt => hlog2.trans_le (hℓ t ht htt)
  have hεpos : ∀ t, 0 < t → t < t₀ → 0 < ε t := fun t ht htt =>
    add_pos (div_pos hC₁pos (hℓpos t ht htt)) (mul_pos hC₁pos ht)
  have hε_le : ∀ t, 0 < t → t < t₀ → ε t ≤ C₁ / Real.log 2 + C₁ := by
    intro t ht htt
    have h1' : t ≤ 1 := by have := htt.le.trans (min_le_right _ _); linarith
    have e1 : C₁ / Real.log t⁻¹ ≤ C₁ / Real.log 2 :=
      div_le_div_of_nonneg_left hC₁pos.le hlog2 (hℓ t ht htt)
    have e2 : C₁ * t ≤ C₁ := by nlinarith
    simp only [hε]
    linarith
  have hε_le' : ∀ t, 0 < t → t < t₀ → ε t ≤ 2 * C₁ / Real.log t⁻¹ := by
    intro t ht htt
    have hl := hℓpos t ht htt
    have htl : t * Real.log t⁻¹ ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (inv_pos.2 ht)
      calc t * Real.log t⁻¹ ≤ t * (t⁻¹ - 1) := mul_le_mul_of_nonneg_left this ht.le
        _ = 1 - t := by rw [mul_sub, mul_inv_cancel₀ ht.ne', mul_one]
        _ ≤ 1 := by linarith
    have e1 : C₁ * t ≤ C₁ / Real.log t⁻¹ := by
      rw [le_div_iff₀ hl]
      nlinarith [mul_le_mul_of_nonneg_left htl hC₁pos.le]
    have e2 : 2 * C₁ / Real.log t⁻¹ = C₁ / Real.log t⁻¹ + C₁ / Real.log t⁻¹ := by ring
    simp only [hε]
    linarith

  have hK : ∀ j, ∀ x ∈ closure (B.mid j),
      B.chart j x ∈ cthickening δ ((B.chart j) '' closure (B.mid j)) :=
    fun j x hx => self_subset_cthickening _ (mem_image_of_mem _ hx)
  have hball' : ∀ t, 0 < t → t < t₀ → ∀ j, ∀ x ∈ closure (B.mid j),
      closedBall (B.chart j x) t ⊆ cthickening δ ((B.chart j) '' closure (B.mid j)) := by
    intro t ht htt j x hx
    have : t ≤ δ := htt.le.trans ((min_le_left _ _).trans (min_le_right _ _))
    exact (closedBall_subset_closedBall this).trans
      (closedBall_subset_cthickening (mem_image_of_mem _ hx) δ)
  have hball : ∀ t, 0 < t → t < t₀ → ∀ j, ∀ x ∈ closure (B.mid j),
      closedBall (B.chart j x) t ⊆ (B.chart j).target :=
    fun t ht htt j x hx => (hball' t ht htt j x hx).trans (hmarg j)

  have hmol := fun j => h3 D ρ (B.chart j).target (B.u j) (B.chart j).open_target (B.u_psh j)
  have hsrc : ∀ j, ∀ x ∈ B.mid j, x ∈ (B.chart j).source :=
    fun j x hx => B.mid_subset_source j hx
  have hu : ∀ j, ∀ x ∈ B.mid j, B.u j (B.chart j x) = B.q j (B.chart j x) + B.ph x := by
    intro j x hx
    simp only [BoundedPshData.u, PotentialCharts.chartFun, (B.chart j).left_inv (hsrc j x hx)]
  have hlow : ∀ t, 0 < t → t < t₀ → ∀ j, ∀ x ∈ B.mid j, B.ph x ≤ B.phReg ρ t j x := by
    intro t ht htt j x hx
    have hz : B.chart j x ∈ shrink (B.chart j).target t :=
      hball t ht htt j x (subset_closure hx)
    have := (((hmol j).1 t ht).2.2.2 _ hz).1
    rw [hu j x hx] at this
    simp only [BoundedPshData.phReg, BoundedPshData.smoothed]
    linarith
  have hupj : ∀ t, 0 < t → t < t₀ → ∀ j, ∀ x ∈ B.mid j, B.phReg ρ t j x ≤ 2 * Q + Cb := by
    intro t ht htt j x hx
    have hz : B.chart j x ∈ shrink (B.chart j).target t :=
      hball t ht htt j x (subset_closure hx)
    have e1 := (((hmol j).1 t ht).2.2.2 _ hz).2
    have e2 : polyMax (B.u j) (B.chart j x) t ≤ Q + Cb := by
      unfold ReciprocityTheory.AnForm.A.polyMax
      apply csSup_le ((nonempty_closedBall.2 ht.le).image _)
      rintro _ ⟨y, hy, rfl⟩
      have f1 := hQ j y (hball' t ht htt j x (subset_closure hx) hy)
      have f2 := hCb ((B.chart j).symm y)
      have f3 := le_abs_self (B.q j y)
      have f4 := le_abs_self (B.ph ((B.chart j).symm y))
      simp only [BoundedPshData.u, PotentialCharts.chartFun]
      linarith
    have e3 := hQ j _ (hK j x (subset_closure hx))
    have e4 := neg_abs_le (B.q j (B.chart j x))
    simp only [BoundedPshData.phReg, BoundedPshData.smoothed]
    linarith
  have hconvj : ∀ j, ∀ x ∈ B.mid j,
      Tendsto (fun t => B.phReg ρ t j x) (𝓝[>] 0) (𝓝 (B.ph x)) := by
    intro j x hx
    have := ((hmol j).2 _ ((B.chart j).map_source (hsrc j x hx))).sub_const
      (B.q j (B.chart j x))
    rw [hu j x hx, add_sub_cancel_left] at this
    exact this

  have hφlow : ∀ t, 0 < t → t < t₀ → ∀ x, B.ph x ≤ B.regularised ρ t (ε t) η x := by
    intro t ht htt x
    obtain ⟨j₀, hj₀⟩ := B.cover x
    have hx₀ : x ∈ B.mid j₀ := B.inner_subset_mid j₀ hj₀
    have hb := regMax_bounds (ι := {j // x ∈ B.mid j}) (hεpos t ht htt)
      (fun j => B.phReg ρ t j x + 4 * ε t * η j x)
    have hle : B.phReg ρ t j₀ x + 4 * ε t * η j₀ x ≤
        tmax (fun j : {j // x ∈ B.mid j} => B.phReg ρ t j x + 4 * ε t * η j x) :=
      Finset.le_sup' (fun j : {j // x ∈ B.mid j} => B.phReg ρ t j x + 4 * ε t * η j x)
        (Finset.mem_univ ⟨j₀, hx₀⟩)
    rw [hη.eq_zero j₀ x hj₀] at hle
    have e1 := hlow t ht htt j₀ x hx₀
    have e2 := (hεpos t ht htt).le
    simp only [BoundedPshData.regularised, PotentialCharts.glue]
    linarith [hb.1]
  have hφup : ∀ t, 0 < t → t < t₀ → ∀ x (M : ℝ), (∀ j, x ∈ B.mid j → B.phReg ρ t j x ≤ M) →
      B.regularised ρ t (ε t) η x ≤ M + ε t := by
    intro t ht htt x M hM
    have hb := regMax_bounds (ι := {j // x ∈ B.mid j}) (hεpos t ht htt)
      (fun j => B.phReg ρ t j x + 4 * ε t * η j x)
    have hle : tmax (fun j : {j // x ∈ B.mid j} => B.phReg ρ t j x + 4 * ε t * η j x) ≤ M :=
      Finset.sup'_le _ _ fun j _ => by
        have e1 := (hη.bounds j.1 x j.2).2
        have e2 := hM j.1 j.2
        have e3 : 4 * ε t * η j x ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith [hεpos t ht htt]) e1
        linarith
    simp only [BoundedPshData.regularised, PotentialCharts.glue]
    linarith [hb.2]

  have hε0 : Tendsto ε (𝓝[>] 0) (𝓝 0) := by
    have hlog : Tendsto (fun t : ℝ => Real.log t⁻¹) (𝓝[>] 0) atTop :=
      Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
    have ha : Tendsto (fun t : ℝ => C₁ / Real.log t⁻¹) (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlog
    have hb : Tendsto (fun t : ℝ => C₁ * t) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => C₁ * t) (𝓝 0) (𝓝 (C₁ * 0)) :=
        tendsto_const_nhds.mul tendsto_id
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have := ha.add hb
    rw [add_zero] at this
    exact this
  have hI : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < t₀ := Ioo_mem_nhdsGT ht₀pos

  have hpt : ∀ x, Tendsto (fun t => B.regularised ρ t (ε t) η x) (𝓝[>] 0) (𝓝 (B.ph x)) := by
    intro x
    rw [tendsto_order]
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · filter_upwards [hI] with t ht
      exact ha.trans_le (hφlow t ht.1 ht.2 x)
    · have hdpos : 0 < (b - B.ph x) / 2 := by linarith
      have hJ : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, x ∈ B.mid j →
          B.phReg ρ t j x ≤ B.ph x + (b - B.ph x) / 2 := by
        rw [eventually_all]
        intro j
        by_cases hx : x ∈ B.mid j
        · filter_upwards [(hconvj j x hx).eventually
            (eventually_le_nhds (by linarith : B.ph x < B.ph x + (b - B.ph x) / 2))] with t ht _
          exact ht
        · exact Eventually.of_forall fun _ h => absurd h hx
      have hE : ∀ᶠ t in 𝓝[>] (0 : ℝ), ε t < (b - B.ph x) / 2 :=
        hε0.eventually (eventually_lt_nhds hdpos)
      filter_upwards [hI, hJ, hE] with t ht hJt hEt
      have := hφup t ht.1 ht.2 x _ hJt
      linarith

  have hcmp' : ∀ t, 0 < t → t < t₀ → ∀ j k, ∀ x ∈ B.mid j ∩ B.mid k,
      |B.phReg ρ t j x - B.phReg ρ t k x| ≤ ε t := by
    intro t ht htt j k x hx
    have hl := hℓpos t ht htt
    have e0 := hcmp t ht (htt.trans_le ((min_le_left _ _).trans (min_le_left _ _))) j k x hx
    have e1 : C₀ / Real.log t⁻¹ ≤ C₁ / Real.log t⁻¹ :=
      div_le_div_of_nonneg_right (le_max_left _ _) hl.le
    have e2 : C₀ * t ≤ C₁ * t := mul_le_mul_of_nonneg_right (le_max_left _ _) ht.le
    simp only [hε]
    linarith
  have hglue := fun t (ht : 0 < t) (htt : t < t₀) =>
    h1 X D A B ρ η Cη t (ε t) hη ht (hεpos t ht htt) (hball t ht htt) (hcmp' t ht htt)
  set Cup : ℝ := 2 * Q + Cb + (C₁ / Real.log 2 + C₁) with hCup
  set C : ℝ := max (8 * max Cη 0 * C₁) Cup with hC
  have hφC : ∀ t, 0 < t → t < t₀ → ∀ x, B.regularised ρ t (ε t) η x ≤ C := by
    intro t ht htt x
    have e1 := hφup t ht htt x (2 * Q + Cb) (fun j hj => hupj t ht htt j x hj)
    have e2 := hε_le t ht htt
    have e3 : Cup ≤ C := le_max_right _ _
    linarith
  have hbd : ∀ t, 0 < t → t < t₀ → ∀ x, |B.regularised ρ t (ε t) η x - B.ph x| ≤ C + Cb := by
    intro t ht htt x
    have e1 := hφlow t ht htt x
    have e2 := hφC t ht htt x
    have e3 := hCb x
    have e4 := neg_abs_le (B.ph x)
    rw [abs_of_nonneg (by linarith)]
    linarith
  refine ⟨C, t₀, fun t => B.regularised ρ t (ε t) η, ht₀pos, ?_, ?_, fun x _ => hpt x⟩
  · intro t ht htt
    refine ⟨(hglue t ht htt).1, fun x => ⟨hφlow t ht htt x, hφC t ht htt x⟩, fun k x hx w => ?_⟩
    have hl := hℓpos t ht htt
    have hgk := (hglue t ht htt).2 k x hx w
    have hw : 0 ≤ ‖w‖ ^ 2 := by positivity
    have key : 4 * Cη * ε t ≤ C / Real.log t⁻¹ := by
      have e0 := (hεpos t ht htt).le
      have e1 : 4 * Cη * ε t ≤ 4 * max Cη 0 * ε t := by
        have := le_max_left Cη 0
        nlinarith
      have e2 : 4 * max Cη 0 * ε t ≤ 4 * max Cη 0 * (2 * C₁ / Real.log t⁻¹) :=
        mul_le_mul_of_nonneg_left (hε_le' t ht htt) (by positivity)
      have e3 : 4 * max Cη 0 * (2 * C₁ / Real.log t⁻¹) = 8 * max Cη 0 * C₁ / Real.log t⁻¹ := by
        ring
      have e4 : 8 * max Cη 0 * C₁ / Real.log t⁻¹ ≤ C / Real.log t⁻¹ :=
        div_le_div_of_nonneg_right (le_max_left _ _) hl.le
      linarith
    exact (mul_le_mul_of_nonneg_right (neg_le_neg key) hw).trans hgk
  · intro k
    have hsub : B.chartMid k ⊆ (B.chart k).target := inter_subset_left
    have hopen : IsOpen (B.chartMid k) :=
      (B.chart k).continuousOn_symm.isOpen_inter_preimage (B.chart k).open_target (B.isOpen_mid k)
    have hmeas : MeasurableSet (B.chartMid k) := hopen.measurableSet
    have hfin : volume (B.chartMid k) ≠ ⊤ :=
      ((isBounded_ball (x := (0 : Fin D → ℂ)) (r := 1)).subset
        (hsub.trans (B.target_subset k))).measure_lt_top.ne
    have : IsFiniteMeasure (volume.restrict (B.chartMid k)) := isFiniteMeasure_restrict.2 hfin
    have hcont : ∀ t, 0 < t → t < t₀ →
        ContinuousOn (fun y => B.regularised ρ t (ε t) η ((B.chart k).symm y)) (B.chartMid k) :=
      fun t ht htt => (continuous_of_atlasSmooth (hglue t ht htt).1).comp_continuousOn
        ((B.chart k).continuousOn_symm.mono hsub)

    have hspos : ∀ n : ℕ, 0 < t₀ / ((n + 2 : ℕ) : ℝ) := fun n => div_pos ht₀pos (by positivity)
    have hslt : ∀ n : ℕ, t₀ / ((n + 2 : ℕ) : ℝ) < t₀ := fun n => by
      rw [div_lt_iff₀ (by positivity)]
      have : (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by push_cast; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      nlinarith
    have hs0 : Tendsto (fun n : ℕ => t₀ / ((n + 2 : ℕ) : ℝ)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨(tendsto_const_div_atTop_nhds_zero_nat t₀).comp
        (tendsto_add_atTop_nat 2), Eventually.of_forall hspos⟩
    have hphm : AEStronglyMeasurable (fun y => B.ph ((B.chart k).symm y))
        (volume.restrict (B.chartMid k)) :=
      aestronglyMeasurable_of_tendsto_ae (u := atTop)
        (fun n => (hcont _ (hspos n) (hslt n)).aestronglyMeasurable hmeas)
        (ae_of_all _ fun y => (hpt _).comp hs0)
    have hdiff : ∀ t, 0 < t → t < t₀ → AEStronglyMeasurable
        (fun y => B.regularised ρ t (ε t) η ((B.chart k).symm y) - B.ph ((B.chart k).symm y))
        (volume.restrict (B.chartMid k)) :=
      fun t ht htt => ((hcont t ht htt).aestronglyMeasurable hmeas).sub hphm
    refine ⟨fun t ht htt => ⟨hdiff t ht htt, ?_⟩, ?_⟩
    · exact MeasureTheory.HasFiniteIntegral.restrict_of_bounded (C := C + Cb) hfin.lt_top
        (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hbd t ht htt _)
    · have hdc := tendsto_integral_filter_of_dominated_convergence
        (μ := volume.restrict (B.chartMid k))
        (F := fun t y => |B.regularised ρ t (ε t) η ((B.chart k).symm y) -
          B.ph ((B.chart k).symm y)|)
        (f := fun _ => 0) (fun _ => C + Cb)
        (hI.mono fun t ht => (hdiff t ht.1 ht.2).norm)
        (hI.mono fun t ht => ae_of_all _ fun y => by
          rw [Real.norm_eq_abs, abs_abs]; exact hbd t ht.1 ht.2 _)
        (integrable_const _)
        (ae_of_all _ fun y => by
          have := ((hpt ((B.chart k).symm y)).sub_const (B.ph ((B.chart k).symm y))).abs
          rw [sub_self, abs_zero] at this
          exact this)
      rw [integral_zero] at hdc
      exact hdc
end BoundedRegularisation
end GroundTheory.Heights₂.Heights.Regular

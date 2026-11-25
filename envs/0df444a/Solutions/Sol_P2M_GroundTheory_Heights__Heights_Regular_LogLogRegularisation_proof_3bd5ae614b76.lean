-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_LogLogRegularisation_proof_3bd5ae614b76
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:11:40.046281+00:00
-- url     : https://prove2.me/submissions/0dd49edc-ee37-4092-8550-e0ca36b638e3

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsChartBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ChartFun
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_LogLogRegularisation_le_glue_6f79181c8cf1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_LogLogRegularisation_glue_le_3755b6feb54c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_mid_subset_source_96b409876f03
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_tmax
import Theorems.Thm_ReciprocityTheory_AnForm_A_mollifierInhabit_thm
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_ge
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_le
import Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_le


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
open Metric Filter Topology
open ReciprocityTheory.AnForm.A (Mollifier tmax regMax le_tmax tmax_le regMax_ge regMax_le)
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.LogLogRegularisation
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : ReciprocityTheory.AnForm.M.FinHolAtlas D X}
namespace GroundTheory.Heights₂.Heights.Regular.LogLogRegularisation
theorem _root_.solution (h0 : GlueRegularised.Statement) (h1 : ChartComparison.Statement)
    (h2 : MollifiedNearSmooth.Statement) (h3 : CutoffsExist.Statement)
    (h4 : ChartMollifiedBounds.Statement) : LogLogRegularisation.Statement := by
  intro X _ _ _ D A R
  obtain ⟨ρ⟩ := ReciprocityTheory.AnForm.A.mollifierInhabit_thm D
  obtain ⟨C1, t1, ht1, hC1⟩ := h1 X D A R ρ
  obtain ⟨C2, t2, ht2, hC2⟩ := h2 X D A R ρ
  obtain ⟨η, Cη, hη⟩ := h3 X D A R.toPotentialCharts
  obtain ⟨C4, t4, ht4, hC4⟩ := h4 X D A R ρ
  obtain ⟨L, hL⟩ := eventually_atTop.1 ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero C2 (1 / 6)
    (by norm_num)).eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (|C2| + 1) by positivity)))
  set E : ℝ := |C1| + 1 with hE
  set Cup : ℝ := |C4| + 2 * E with hCup
  set C : ℝ := Cup + (|C1| + |C2| + |C4|) + 8 * |Cη| * E + 2 * E + |R.Clog| with hC
  have hE0 : 0 ≤ E := by positivity
  have hCup0 : 0 ≤ Cup := by positivity
  refine ⟨C, max (max L (Real.exp 1)) (max (-Real.log t1) (max (-Real.log t2) (-Real.log t4)) + 1),
    fun t ht hℓ => ?_⟩
  set ℓ := Real.log t⁻¹ with hℓdef
  have hℓL : L ≤ ℓ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hℓ
  have hℓe : Real.exp 1 ≤ ℓ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hℓ
  have hℓt : max (-Real.log t1) (max (-Real.log t2) (-Real.log t4)) + 1 ≤ ℓ :=
    le_trans (le_max_right _ _) hℓ
  have hℓ0 : 0 < ℓ := (Real.exp_pos 1).trans_le hℓe
  have hlogt : Real.log t = -ℓ := by rw [hℓdef, Real.log_inv, neg_neg]
  have hlt : ∀ s, 0 < s → -Real.log s + 1 ≤ ℓ → t < s := fun s hs h =>
    (Real.log_lt_log_iff ht hs).1 (by linarith)
  have htt1 : t < t1 := hlt t1 ht1 (le_trans (by simp) hℓt)
  have htt2 : t < t2 := hlt t2 ht2 (le_trans (by simp) hℓt)
  have htt4 : t < t4 := hlt t4 ht4 (le_trans (by simp) hℓt)
  have hlog1 : 1 ≤ Real.log ℓ := by
    rw [Real.le_log_iff_exp_le hℓ0]; exact hℓe
  set q := Real.log ℓ / ℓ with hqdef
  have hq0 : 0 ≤ q := div_nonneg (by linarith) hℓ0.le
  have hq1 : q ≤ 1 := (div_le_one hℓ0).2 (by linarith [Real.log_le_sub_one_of_pos hℓ0])
  have htexp : t = Real.exp (-ℓ) := by rw [← hlogt, Real.exp_log ht]
  have htq : t ≤ q := by
    rw [htexp, Real.exp_neg, hqdef]
    rw [inv_le_iff_one_le_mul₀ (Real.exp_pos ℓ)]
    have h5 : ℓ + 1 ≤ Real.exp ℓ := Real.add_one_le_exp ℓ
    have h6 : 1 ≤ Real.exp ℓ * (Real.log ℓ / ℓ) := by
      rw [mul_div_assoc', le_div_iff₀ hℓ0, one_mul]
      have := le_mul_of_one_le_right (Real.exp_pos ℓ).le hlog1
      linarith
    rw [mul_comm]; exact h6
  have hCq : ∀ c : ℝ, c * Real.log ℓ / ℓ = c * q := fun c => by rw [hqdef, mul_div_assoc]

  set K : ℝ := (|C1| + |C2|) * Real.log ℓ with hK
  have hK0 : 0 ≤ K := by positivity
  have hlog0 : 0 ≤ Real.log ℓ := by linarith
  have hK1 : C1 * Real.log ℓ ≤ K := by
    have := mul_le_mul_of_nonneg_right (le_abs_self C1) hlog0
    have := mul_nonneg (abs_nonneg C2) hlog0
    rw [hK]; linarith
  have hK2 : C2 * Real.log ℓ ≤ K := by
    have := mul_le_mul_of_nonneg_right (le_abs_self C2) hlog0
    have := mul_nonneg (abs_nonneg C1) hlog0
    rw [hK]; linarith
  set ε : ℝ := E * (q + t) with hεdef
  have hε : 0 < ε := by positivity
  have hε2 : ε ≤ 2 * E * q := by
    have := mul_le_mul_of_nonneg_left htq hE0
    rw [hεdef]; linarith
  have hεE : ε ≤ 2 * E := by
    have := mul_le_mul_of_nonneg_left hq1 hE0
    linarith
  have hterm : 0 ≤ 8 * |Cη| * E := by positivity
  have hClog0 : 0 ≤ |R.Clog| := abs_nonneg _
  have ha1 := abs_nonneg C1
  have ha2 := abs_nonneg C2
  have ha4 := abs_nonneg C4
  have hcomp : ∀ j k, ∀ x ∈ R.mid j ∩ R.mid k, |R.phReg ρ K t j x - R.phReg ρ K t k x| ≤ ε := by
    intro j k x hx
    refine (hC1 t ht htt1 K hK1 j k x hx).trans ?_
    rw [hCq]
    have hC1E : C1 ≤ E := by linarith [le_abs_self C1]
    have := mul_le_mul_of_nonneg_right hC1E hq0
    have := mul_le_mul_of_nonneg_right hC1E ht.le
    rw [hεdef]; linarith
  obtain ⟨hball, hbd⟩ := hC4 t ht htt4
  obtain ⟨hsmooth, hlevi⟩ := h0 X D A R ρ η Cη K t ε hη ht hε hball hcomp
  set φt := R.regularised ρ K t ε η with hφt
  have harg : ∀ j x, x ∈ R.mid j → R.phReg ρ K t j x + 4 * ε * η j x ≤ R.phReg ρ K t j x :=
    fun j x hx => by
      have := mul_nonpos_of_nonneg_of_nonpos (by positivity : (0 : ℝ) ≤ 4 * ε) (hη.bounds j x hx).2
      linarith
  have hup : ∀ x, φt x ≤ Cup := by
    intro x
    refine (glue_le R.toPotentialCharts _ hε.le (c := C4) fun j hx =>
      (harg j x hx).trans (hbd K hK0 j x hx).2.1).trans ?_
    rw [hCup]; linarith [le_abs_self C4]
  have hlow : ∀ x, ∃ k, x ∈ R.mid k ∧ R.phReg ρ K t k x ≤ φt x := by
    intro x
    obtain ⟨k, hk⟩ := R.cover x
    have hkm := R.inner_subset_mid k hk
    refine ⟨k, hkm, ?_⟩
    have := le_glue R.toPotentialCharts
      (fun j x => R.phReg ρ K t j x + 4 * ε * η j x) hε.le hkm
    have e : φt x = R.glue (fun j x => R.phReg ρ K t j x + 4 * ε * η j x) ε x := rfl
    rw [e]
    simpa [hη.eq_zero k x hk] using this
  have hCbig : |C1| + |C2| + |C4| ≤ C := by
    rw [hC]; linarith
  have hC0 : 0 ≤ C := le_trans (by positivity) hCbig

  have hd1 : ∀ x ∈ R.Yo, R.r x ≤ ℓ → φt x ≤ R.ph x + t ^ (1 / 3 : ℝ) + C * q := by
    intro x hxY hr
    have hnear : ∀ j, x ∈ R.mid j → R.phReg ρ K t j x + 4 * ε * η j x ≤
        R.ph x + C2 * ℓ ^ C2 * t ^ (1 / 2 : ℝ) := by
      intro j hx
      refine (harg j x hx).trans ?_
      have h := hC2 t ht htt2 K hK2 j x ⟨hx, hxY⟩ hr
      have hsrc := R.mid_subset_source j hx
      simp only [RegChartData.u, PotentialCharts.chartFun, (R.chart j).left_inv hsrc] at h
      simp only [RegChartData.phReg]
      linarith
    have hg := glue_le R.toPotentialCharts (fun j x => R.phReg ρ K t j x + 4 * ε * η j x) hε.le hnear
    have e : φt x = R.glue (fun j x => R.phReg ρ K t j x + 4 * ε * η j x) ε x := rfl
    rw [← e] at hg
    have h16 : t ^ (1 / 6 : ℝ) = Real.exp (-(1 / 6) * ℓ) := by
      rw [Real.rpow_def_of_pos ht, hlogt]; congr 1; ring
    have hsplit : t ^ (1 / 2 : ℝ) = t ^ (1 / 3 : ℝ) * t ^ (1 / 6 : ℝ) := by
      rw [← Real.rpow_add ht]; norm_num
    have hP := hL ℓ hℓL
    set P := ℓ ^ C2 * Real.exp (-(1 / 6) * ℓ) with hPdef
    have hP0 : 0 ≤ P := mul_nonneg (Real.rpow_nonneg hℓ0.le _) (Real.exp_pos _).le
    have hCP : C2 * P ≤ 1 := by
      have h7 : |C2| * P ≤ |C2| * (1 / (|C2| + 1)) :=
        mul_le_mul_of_nonneg_left hP.le (abs_nonneg _)
      have h8 : |C2| * (1 / (|C2| + 1)) ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]; linarith
      have := mul_le_mul_of_nonneg_right (le_abs_self C2) hP0
      linarith
    have h13 : 0 ≤ t ^ (1 / 3 : ℝ) := Real.rpow_nonneg ht.le _
    have hkey : C2 * ℓ ^ C2 * t ^ (1 / 2 : ℝ) ≤ t ^ (1 / 3 : ℝ) := by
      rw [hsplit, h16]
      have : C2 * ℓ ^ C2 * (t ^ (1 / 3 : ℝ) * Real.exp (-(1 / 6) * ℓ)) =
          (C2 * P) * t ^ (1 / 3 : ℝ) := by rw [hPdef]; ring
      rw [this]; exact mul_le_of_le_one_left h13 hCP
    have hεC : ε ≤ C * q := by
      refine hε2.trans (mul_le_mul_of_nonneg_right ?_ hq0)
      rw [hC]; linarith
    linarith
  refine ⟨φt, hsmooth, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x hxY
    obtain ⟨k, hk, hle⟩ := hlow x
    exact ((hbd K hK0 k x hk).2.2 hxY).trans hle
  ·
    intro x
    exact (hup x).trans (by rw [hC]; linarith)
  ·
    intro x
    obtain ⟨k, hk, hle⟩ := hlow x
    have h := (hbd K hK0 k x hk).1
    have h9 := mul_le_mul_of_nonneg_right hCbig hlog0
    have h10 := le_mul_of_one_le_right (abs_nonneg C4) hlog1
    have h11 := le_abs_self C4
    linarith
  ·
    intro k x hx w
    refine le_trans ?_ (hlevi k x hx w)
    rw [hCq]
    have hw : 0 ≤ ‖w‖ ^ 2 := by positivity
    have h11 : 4 * Cη * ε ≤ 8 * |Cη| * E * q := by
      have h12 := mul_le_mul_of_nonneg_right (by linarith [le_abs_self Cη] : 4 * Cη ≤ 4 * |Cη|) hε.le
      have h13 := mul_le_mul_of_nonneg_left hε2 (by positivity : (0 : ℝ) ≤ 4 * |Cη|)
      linarith
    have h14 : 8 * |Cη| * E * q ≤ C * q := by
      refine mul_le_mul_of_nonneg_right ?_ hq0
      rw [hC]; linarith
    have h15 := mul_le_mul_of_nonneg_right (h11.trans h14) hw
    linarith
  ·
    intro x hxY hr
    rw [hCq]
    exact hd1 x hxY hr
  ·
    intro x hxY
    rw [hCq]
    have hr1 := R.one_le_r x hxY
    have hr0 : 0 < R.r x := by linarith
    have h13 : 0 ≤ t ^ (1 / 3 : ℝ) := Real.rpow_nonneg ht.le _
    by_cases hr : R.r x ≤ ℓ
    · have := hd1 x hxY hr
      have := le_mul_of_one_le_right (mul_nonneg hC0 hq0) hr1
      linarith
    · push Not at hr
      have hlogr : Real.log (R.r x) ≤ q * R.r x := by
        have h15 := Real.log_div_self_antitoneOn (Set.mem_Ici.2 hℓe)
          (Set.mem_Ici.2 (hℓe.trans hr.le)) hr.le
        simp only at h15
        rw [div_le_iff₀ hr0] at h15
        exact h15
      have hqr : 1 ≤ q * R.r x := by
        have e1 : q * ℓ = Real.log ℓ := by rw [hqdef]; field_simp
        have := mul_le_mul_of_nonneg_left hr.le hq0
        linarith
      have hph := R.ph_ge x hxY
      have hlr0 : 0 ≤ Real.log (R.r x) := Real.log_nonneg hr1
      have h16 : -R.Clog * Real.log (R.r x) ≥ -|R.Clog| * Real.log (R.r x) := by
        have := mul_le_mul_of_nonneg_right (le_abs_self R.Clog) hlr0
        linarith
      have h17 : Cup + |R.Clog| * Real.log (R.r x) ≤ C * q * R.r x := by
        have h18 : Cup ≤ Cup * (q * R.r x) := le_mul_of_one_le_right hCup0 hqr
        have h19 : |R.Clog| * Real.log (R.r x) ≤ |R.Clog| * (q * R.r x) :=
          mul_le_mul_of_nonneg_left hlogr (abs_nonneg _)
        have h20 : Cup + |R.Clog| ≤ C := by
          rw [hC]; linarith [abs_nonneg C1, abs_nonneg C2, abs_nonneg C4]
        have h21 : 0 ≤ q * R.r x := by positivity
        have := mul_le_mul_of_nonneg_right h20 h21
        linarith
      have := hup x
      linarith
end GroundTheory.Heights₂.Heights.Regular.LogLogRegularisation

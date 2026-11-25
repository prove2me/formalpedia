-- Prove2me | solution 1 for PI.AprimeInfG.tube_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:59:36.871857+00:00
-- url     : https://prove2.me/submissions/3d54453b-8ec4-42fe-be97-2cf0591e81f3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_LintegralMulRightOfMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_GrpTube
import Theorems.Thm_PI_AprimeInfG_tube_meas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfG
open MeasureTheory Topology Filter Metric Set
open scoped ENNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
namespace PI.AprimeInfG
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant]
    [SFinite ν] (hν0 : ν univ ≠ 0) (hνf : ν univ ≠ ∞) {ι η : Type} [Fintype ι] [Fintype η]
    {κ : EuclideanSpace ℝ ι → G} {χ : EuclideanSpace ℝ η → H} {r0 : ℝ} {d : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ}
    {e : EuclideanSpace ℝ η → ℝ} (hC : TubeChart μ H ν κ χ r0 d e)
    {ε s ρ : ℝ} (hε : 0 < ε) (hεd : ε < d 0) (hεe : ε < e 0) (hs : 0 < s) (hsr : s ≤ r0) (hρ : 0 < ρ)
    (hρs : ρ ≤ s) (hdε : ∀ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η, ‖p‖ < s → |d p - d 0| < ε)
    (heε : ∀ y : EuclideanSpace ℝ η, ‖y‖ < s → |e y - e 0| < ε) :
    0 < μ (tubeS H (κ '' ball 0 ρ) univ) ∧ μ (tubeS H (κ '' ball 0 ρ) univ) < ⊤ ∧
    (d 0 - ε) / (e 0 + ε) * (ν univ).toReal ≤
      (μ (tubeS H (κ '' ball 0 ρ) univ)).toReal / (volume (ball (0 : EuclideanSpace ℝ ι) ρ)).toReal ∧
    (μ (tubeS H (κ '' ball 0 ρ) univ)).toReal / (volume (ball (0 : EuclideanSpace ℝ ι) ρ)).toReal ≤
      (d 0 + ε) / (e 0 - ε) * (ν univ).toReal := by
  have hρr : ρ ≤ r0 := hρs.trans hsr
  set A := ball (0 : EuclideanSpace ℝ ι) ρ ×ˢ ball (0 : EuclideanSpace ℝ η) s with hA
  have hAm : MeasurableSet A := measurableSet_ball.prod measurableSet_ball
  have hAn : ∀ p ∈ A, ‖p‖ < s := by
    intro p hp
    rw [Prod.norm_def]
    have h1 : ‖p.1‖ < ρ := mem_ball_zero_iff.1 hp.1
    have h2 : ‖p.2‖ < s := mem_ball_zero_iff.1 hp.2
    exact max_lt (h1.trans_le hρs) h2
  set Lρ := volume (ball (0 : EuclideanSpace ℝ ι) ρ) with hLρ
  set Ls := volume (ball (0 : EuclideanSpace ℝ η) s) with hLs
  have hLρ0 : 0 < Lρ := measure_ball_pos _ _ hρ
  have hLs0 : 0 < Ls := measure_ball_pos _ _ hs
  have hLρt : Lρ < ⊤ := measure_ball_lt_top
  have hLst : Ls < ⊤ := measure_ball_lt_top
  have hvA : volume A = Lρ * Ls := by rw [hA, Measure.volume_eq_prod, Measure.prod_prod]

  have hVS_hi : μ (tubeS H (κ '' ball 0 ρ) (χ '' ball 0 s)) ≤ ENNReal.ofReal (d 0 + ε) * (Lρ * Ls) := by
    rw [hC.densG ρ s hρ hρr hs hsr, ← hvA, ← setLIntegral_const]
    refine setLIntegral_mono' hAm fun p hp => ENNReal.ofReal_le_ofReal ?_
    have := abs_lt.1 (hdε p (hAn p hp)); linarith
  have hVS_lo : ENNReal.ofReal (d 0 - ε) * (Lρ * Ls) ≤ μ (tubeS H (κ '' ball 0 ρ) (χ '' ball 0 s)) := by
    rw [hC.densG ρ s hρ hρr hs hsr, ← hvA, ← setLIntegral_const]
    refine setLIntegral_mono' hAm fun p hp => ENNReal.ofReal_le_ofReal ?_
    have := abs_lt.1 (hdε p (hAn p hp)); linarith
  have hS_hi : ν (χ '' ball 0 s) ≤ ENNReal.ofReal (e 0 + ε) * Ls := by
    rw [hC.densH s hs hsr, ← setLIntegral_const]
    refine setLIntegral_mono' measurableSet_ball fun y hy => ENNReal.ofReal_le_ofReal ?_
    have := abs_lt.1 (heε y (mem_ball_zero_iff.1 hy)); linarith
  have hS_lo : ENNReal.ofReal (e 0 - ε) * Ls ≤ ν (χ '' ball 0 s) := by
    rw [hC.densH s hs hsr, ← setLIntegral_const]
    refine setLIntegral_mono' measurableSet_ball fun y hy => ENNReal.ofReal_le_ofReal ?_
    have := abs_lt.1 (heε y (mem_ball_zero_iff.1 hy)); linarith

  have hV : ∀ a ∈ κ '' ball (0 : EuclideanSpace ℝ ι) ρ, ∀ b ∈ κ '' ball (0 : EuclideanSpace ℝ ι) ρ,
      a⁻¹ * b ∈ H → a = b := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hm
    rw [hC.inj x (ball_subset_ball hρr hx) y (ball_subset_ball hρr hy) hm]
  have hid := tube_meas μ H ν hν0 hνf hV (hC.mS s hs hsr) (hC.mT ρ s hρ hρr hs hsr) (hC.mH ρ hρ hρr)
  set N := ν univ with hN
  set a := μ (tubeS H (κ '' ball 0 ρ) (χ '' ball 0 s)) with ha
  set b := μ (tubeS H (κ '' ball 0 ρ) univ) with hb
  set c := ν (χ '' ball 0 s) with hc
  have hde : 0 < d 0 - ε := by linarith
  have hee : 0 < e 0 - ε := by linarith
  have hat : a ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top hLρt.ne hLst.ne)) hVS_hi
  have ha0 : a ≠ 0 := by
    apply ne_of_gt
    refine lt_of_lt_of_le ?_ hVS_lo
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 hde).ne' (ENNReal.mul_pos hLρ0.ne' hLs0.ne').ne'
  have hct : c ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLst.ne) hS_hi
  have hc0 : c ≠ 0 := by
    apply ne_of_gt
    refine lt_of_lt_of_le ?_ hS_lo
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 hee).ne' hLs0.ne'
  have hbt : b ≠ ⊤ := by
    intro hb'
    have : N * a = ⊤ := by rw [hid, hb', ENNReal.mul_top hc0]
    exact ENNReal.mul_ne_top hνf hat this
  have hb0 : b ≠ 0 := by
    intro hb'
    have : N * a = 0 := by rw [hid, hb', mul_zero]
    rcases mul_eq_zero.1 this with h | h
    · exact hν0 h
    · exact ha0 h
  refine ⟨pos_iff_ne_zero.2 hb0, lt_top_iff_ne_top.2 hbt, ?_, ?_⟩
  all_goals
    have hidR : N.toReal * a.toReal = c.toReal * b.toReal := by
      rw [← ENNReal.toReal_mul, ← ENNReal.toReal_mul, hid]
    have hlρ : 0 < Lρ.toReal := ENNReal.toReal_pos hLρ0.ne' hLρt.ne
    have hls : 0 < Ls.toReal := ENNReal.toReal_pos hLs0.ne' hLst.ne
    have hNr : 0 < N.toReal := ENNReal.toReal_pos hν0 hνf
    have hbr : 0 < b.toReal := ENNReal.toReal_pos hb0 hbt
    have ahi : a.toReal ≤ (d 0 + ε) * (Lρ.toReal * Ls.toReal) := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top hLρt.ne hLst.ne)) hVS_hi
      rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this
    have alo : (d 0 - ε) * (Lρ.toReal * Ls.toReal) ≤ a.toReal := by
      have := ENNReal.toReal_mono hat hVS_lo
      rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hde.le] at this
    have chi : c.toReal ≤ (e 0 + ε) * Ls.toReal := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLst.ne) hS_hi
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this
    have clo : (e 0 - ε) * Ls.toReal ≤ c.toReal := by
      have := ENNReal.toReal_mono hct hS_lo
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hee.le] at this
  ·
    rw [le_div_iff₀ hlρ, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    have h1 : N.toReal * ((d 0 - ε) * (Lρ.toReal * Ls.toReal)) ≤ b.toReal * ((e 0 + ε) * Ls.toReal) :=
      calc N.toReal * ((d 0 - ε) * (Lρ.toReal * Ls.toReal)) ≤ N.toReal * a.toReal :=
            mul_le_mul_of_nonneg_left alo hNr.le
        _ = c.toReal * b.toReal := hidR
        _ ≤ ((e 0 + ε) * Ls.toReal) * b.toReal := mul_le_mul_of_nonneg_right chi hbr.le
        _ = b.toReal * ((e 0 + ε) * Ls.toReal) := mul_comm _ _
    have h2 : ((d 0 - ε) * N.toReal * Lρ.toReal) * Ls.toReal ≤ (b.toReal * (e 0 + ε)) * Ls.toReal := by
      nlinarith
    exact le_of_mul_le_mul_right h2 hls
  ·
    rw [div_le_iff₀ hlρ, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hee]
    have h1 : b.toReal * ((e 0 - ε) * Ls.toReal) ≤ N.toReal * ((d 0 + ε) * (Lρ.toReal * Ls.toReal)) :=
      calc b.toReal * ((e 0 - ε) * Ls.toReal) = ((e 0 - ε) * Ls.toReal) * b.toReal := mul_comm _ _
        _ ≤ c.toReal * b.toReal := mul_le_mul_of_nonneg_right clo hbr.le
        _ = N.toReal * a.toReal := hidR.symm
        _ ≤ N.toReal * ((d 0 + ε) * (Lρ.toReal * Ls.toReal)) := mul_le_mul_of_nonneg_left ahi hNr.le
    have h2 : (b.toReal * (e 0 - ε)) * Ls.toReal ≤ ((d 0 + ε) * N.toReal * Lρ.toReal) * Ls.toReal := by
      nlinarith
    exact le_of_mul_le_mul_right h2 hls
end PI.AprimeInfG

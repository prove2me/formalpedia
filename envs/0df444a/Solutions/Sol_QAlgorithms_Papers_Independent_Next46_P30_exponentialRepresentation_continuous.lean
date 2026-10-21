-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P30.exponentialRepresentation_continuous
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T14:39:18.620417+00:00
-- url     : https://prove2.me/submissions/86091031-c6f9-4bd2-989f-e9e072570b95

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P30
noncomputable section

open MeasureTheory Filter Topology Metric

open QAlgorithms.Papers.Independent.Next46.P30

open scoped ENNReal

lemma g61b_norm_of_ae (u : HilbertSpace) (F : ℝ → ℂ) (h : (u : ℝ → ℂ) =ᵐ[intervalMeasure] F) :
    ‖u‖ = (eLpNorm F 2 intervalMeasure).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae h]

lemma g61b_sub_ae (f g : GroupSpace) (xi eta : HilbertSpace) :
    ((phaseAction f xi - phaseAction g eta : HilbertSpace) : ℝ → ℂ) =ᵐ[intervalMeasure]
      fun t => phaseProduct f xi t - phaseProduct g eta t := by
  filter_upwards [Lp.coeFn_sub (phaseAction f xi) (phaseAction g eta),
    (MemLp.coeFn_toLp _ : (phaseAction f xi : ℝ → ℂ) =ᵐ[intervalMeasure] phaseProduct f xi),
    (MemLp.coeFn_toLp _ : (phaseAction g eta : ℝ → ℂ) =ᵐ[intervalMeasure] phaseProduct g eta)]
    with t h1 h2 h3
  rw [h1, Pi.sub_apply]
  exact congrArg₂ (· - ·) h2 h3

lemma g61b_isometry (f : GroupSpace) (xi eta : HilbertSpace) :
    ‖phaseAction f xi - phaseAction f eta‖ = ‖xi - eta‖ := by
  rw [g61b_norm_of_ae _ _ (g61b_sub_ae f f xi eta), Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [Lp.coeFn_sub xi eta] with t ht
  rw [ht, Pi.sub_apply]
  simp only [phaseProduct, ← mul_sub, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]

lemma g61b_exp_diff (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ ≤ |a - b| := by
  have : Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ)) =
      Complex.exp (Complex.I * (b : ℂ)) * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [this, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)
  simpa [Real.norm_eq_abs] using this

lemma g61b_pointwise (a b : ℝ) (z : ℂ) (M : ℝ) (hM : 0 < M) :
    ‖(Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))) * z‖ ≤
      2 * ‖({w : ℂ | M ≤ ‖w‖₊}.indicator id z)‖ + M * ‖a - b‖ := by
  rw [norm_mul]
  by_cases hz : M ≤ ‖z‖₊
  · rw [Set.indicator_of_mem (show z ∈ {w : ℂ | M ≤ ‖w‖₊} from hz), id]
    have h1 : ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ ≤ 2 := by
      calc _ ≤ ‖Complex.exp (Complex.I * (a : ℂ))‖ + ‖Complex.exp (Complex.I * (b : ℂ))‖ :=
            norm_sub_le _ _
        _ = 2 := by rw [Complex.norm_exp_I_mul_ofReal, Complex.norm_exp_I_mul_ofReal]; norm_num
    have : 0 ≤ M * ‖a - b‖ := by positivity
    nlinarith [norm_nonneg z]
  · rw [Set.indicator_of_notMem (show z ∉ {w : ℂ | M ≤ ‖w‖₊} from hz)]
    have hz' : ‖z‖ ≤ M := by
      have : (‖z‖₊ : ℝ) < M := lt_of_not_ge hz
      exact this.le
    have h1 := g61b_exp_diff a b
    rw [norm_zero, mul_zero, zero_add, Real.norm_eq_abs]
    calc _ ≤ |a - b| * M := mul_le_mul h1 hz' (norm_nonneg _) (abs_nonneg _)
      _ = M * |a - b| := mul_comm _ _

lemma g61b_unif (eta : HilbertSpace) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ f g : GroupSpace,
      ‖phaseAction f eta - phaseAction g eta‖ ≤ ε + M * ‖f - g‖ := by
  obtain ⟨M, hM, hI⟩ := (Lp.memLp eta).eLpNorm_indicator_norm_ge_pos_le
    (Lp.stronglyMeasurable eta) (ε := ε / 2) (by positivity)
  refine ⟨M, hM, fun f g => ?_⟩
  set I : ℝ → ℂ := {x | M ≤ ‖(eta : ℝ → ℂ) x‖₊}.indicator (eta : ℝ → ℂ) with hIdef
  have hIfin : eLpNorm I 2 intervalMeasure < ∞ := lt_of_le_of_lt hI ENNReal.ofReal_lt_top
  have hIm : AEStronglyMeasurable I intervalMeasure :=
    (Lp.aestronglyMeasurable eta).indicator
      (measurableSet_le measurable_const (Lp.stronglyMeasurable eta).measurable.nnnorm.coe_nnreal_real)
  have hfg : AEStronglyMeasurable (fun t => (f : ℝ → ℝ) t - (g : ℝ → ℝ) t) intervalMeasure :=
    (Lp.aestronglyMeasurable f).sub (Lp.aestronglyMeasurable g)
  have hfgn : eLpNorm (fun t => (f : ℝ → ℝ) t - (g : ℝ → ℝ) t) 2 intervalMeasure =
      eLpNorm (⇑(f - g)) 2 intervalMeasure := by
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_sub f g] with t ht
    rw [ht, Pi.sub_apply]
  have hfgfin : eLpNorm (⇑(f - g)) 2 intervalMeasure < ∞ := Lp.eLpNorm_lt_top _
  rw [g61b_norm_of_ae _ _ (g61b_sub_ae f g eta eta)]
  have hbound : eLpNorm (fun t => phaseProduct f eta t - phaseProduct g eta t) 2 intervalMeasure ≤
      eLpNorm (fun t => 2 * ‖I t‖ + M * ‖(f : ℝ → ℝ) t - (g : ℝ → ℝ) t‖) 2 intervalMeasure := by
    apply eLpNorm_mono_real
    intro t
    have := g61b_pointwise ((f : ℝ → ℝ) t) ((g : ℝ → ℝ) t) ((eta : ℝ → ℂ) t) M hM
    simp only [phaseProduct, ← sub_mul]
    convert this using 3
    simp only [hIdef, Set.indicator, id, coe_nnnorm, Set.mem_setOf_eq]
  have hsum : eLpNorm (fun t => 2 * ‖I t‖ + M * ‖(f : ℝ → ℝ) t - (g : ℝ → ℝ) t‖) 2
      intervalMeasure ≤ ENNReal.ofReal 2 * eLpNorm I 2 intervalMeasure +
        ENNReal.ofReal M * eLpNorm (⇑(f - g)) 2 intervalMeasure := by
    refine (eLpNorm_add_le ?_ ?_ (by norm_num)).trans ?_
    · exact (hIm.norm.const_mul 2)
    · exact (hfg.norm.const_mul M)
    gcongr
    · rw [show (fun t => 2 * ‖I t‖) = (2 : ℝ) • (fun t => ‖I t‖) from rfl, eLpNorm_const_smul,
        eLpNorm_norm]
      simp [Real.enorm_eq_ofReal]
    · rw [show (fun t => M * ‖(f : ℝ → ℝ) t - (g : ℝ → ℝ) t‖) =
          M • (fun t => ‖(f : ℝ → ℝ) t - (g : ℝ → ℝ) t‖) from rfl, eLpNorm_const_smul,
        eLpNorm_norm, hfgn]
      simp [Real.enorm_eq_ofReal hM.le]
  have htot := hbound.trans hsum
  have hfinR : ENNReal.ofReal 2 * eLpNorm I 2 intervalMeasure +
      ENNReal.ofReal M * eLpNorm (⇑(f - g)) 2 intervalMeasure ≠ ∞ := by
    apply ENNReal.add_ne_top.2 ⟨?_, ?_⟩
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIfin.ne
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfgfin.ne
  calc _ ≤ (ENNReal.ofReal 2 * eLpNorm I 2 intervalMeasure +
        ENNReal.ofReal M * eLpNorm (⇑(f - g)) 2 intervalMeasure).toReal :=
        ENNReal.toReal_mono hfinR htot
    _ = 2 * (eLpNorm I 2 intervalMeasure).toReal + M * ‖f - g‖ := by
        rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIfin.ne)
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfgfin.ne), ENNReal.toReal_mul,
          ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal hM.le,
          Lp.norm_def]
    _ ≤ ε + M * ‖f - g‖ := by
        have : (eLpNorm I 2 intervalMeasure).toReal ≤ ε / 2 := by
          have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hI
          rwa [ENNReal.toReal_ofReal (by positivity)] at this
        linarith

theorem g61b_cont :
    Continuous (fun z : GroupSpace × HilbertSpace => phaseAction z.1 z.2) := by
  rw [Metric.continuous_iff]
  rintro ⟨f0, xi0⟩ ε hε
  obtain ⟨M, hM, hU⟩ := g61b_unif xi0 (ε / 4) (by positivity)
  refine ⟨min (ε / 4) (ε / (4 * M)), by positivity, ?_⟩
  rintro ⟨f, xi⟩ hd
  have hd1 : dist f f0 < min (ε / 4) (ε / (4 * M)) := lt_of_le_of_lt (le_max_left _ _) hd
  have hd2 : dist xi xi0 < min (ε / 4) (ε / (4 * M)) := lt_of_le_of_lt (le_max_right _ _) hd
  rw [dist_eq_norm] at hd1 hd2 ⊢
  have e1 := g61b_isometry f xi xi0
  have e2 := hU f f0
  have hm1 : ‖f - f0‖ < ε / (4 * M) := lt_of_lt_of_le hd1 (min_le_right _ _)
  have hm2 : ‖xi - xi0‖ < ε / 4 := lt_of_lt_of_le hd2 (min_le_left _ _)
  have hMf : M * ‖f - f0‖ ≤ ε / 4 := by
    have := mul_lt_mul_of_pos_left hm1 hM
    rw [show M * (ε / (4 * M)) = ε / 4 by field_simp] at this
    exact this.le
  calc ‖phaseAction f xi - phaseAction f0 xi0‖
      ≤ ‖phaseAction f xi - phaseAction f xi0‖ + ‖phaseAction f xi0 - phaseAction f0 xi0‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε := by linarith

theorem solution :
    Continuous (fun z : GroupSpace × HilbertSpace => phaseAction z.1 z.2) := g61b_cont

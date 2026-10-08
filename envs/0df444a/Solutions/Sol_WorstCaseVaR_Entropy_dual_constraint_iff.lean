-- Prove2me | solution 1 for WorstCaseVaR.Entropy.dual_constraint_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T06:51:36.067978+00:00
-- url     : https://prove2.me/submissions/e24321dd-4e40-4215-bffe-e3007ffda9f7

import Mathlib
import Definitions.Def_WorstCaseVaR_Entropy_Basic



namespace WorstCaseVaR.Entropy

open MeasureTheory ProbabilityTheory Filter Topology

/-- The standard normal CDF is continuous. -/
lemma aux_kz_cont : Continuous stdNormalCDF := by
  have hmono : Monotone (cdf (gaussianReal 0 1)) := monotone_cdf _
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hleft : ∀ b : ℝ, Function.leftLim (cdf (gaussianReal 0 1)) b = cdf (gaussianReal 0 1) b := by
    intro b
    have h1 := (cdf (gaussianReal 0 1)).measure_singleton b
    rw [measure_cdf, measure_singleton] at h1
    have h2 : cdf (gaussianReal 0 1) b - Function.leftLim (cdf (gaussianReal 0 1)) b ≤ 0 :=
      ENNReal.ofReal_eq_zero.mp h1.symm
    have h3 := hmono.leftLim_le (le_refl b)
    linarith
  have : Continuous (cdf (gaussianReal 0 1)) := by
    rw [continuous_iff_continuousAt]
    intro b
    rw [continuousAt_iff_continuous_left_right]
    refine ⟨?_, (cdf (gaussianReal 0 1)).right_continuous b⟩
    rw [← continuousWithinAt_Iio_iff_Iic]
    exact (hmono.continuousWithinAt_Iio_iff_leftLim_eq).2 (hleft b)
  exact this

/-- Strict monotonicity of the quantile on `(0,1)`. -/
lemma aux_kz_quant {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1) :
    normalQuantile p < normalQuantile q := by
  have hc := aux_kz_cont
  set Sp := {t : ℝ | p ≤ stdNormalCDF t} with hSp
  set Sq := {t : ℝ | q ≤ stdNormalCDF t} with hSq
  -- nonempty
  have hne : Sq.Nonempty := by
    have ht : Tendsto stdNormalCDF atTop (𝓝 1) := tendsto_cdf_atTop _
    have := (ht.eventually (lt_mem_nhds hq)).exists
    obtain ⟨t, ht⟩ := this
    exact ⟨t, le_of_lt ht⟩
  -- bdd below
  have hbddp : BddBelow Sp := by
    have ht : Tendsto stdNormalCDF atBot (𝓝 0) := tendsto_cdf_atBot _
    obtain ⟨T, hT⟩ := eventually_atBot.1 (ht.eventually (gt_mem_nhds hp))
    refine ⟨T, fun t htS => ?_⟩
    by_contra hlt
    push_neg at hlt
    have := hT t hlt.le
    have h2 : p ≤ stdNormalCDF t := htS
    linarith
  have hsub : Sq ⊆ Sp := fun t (ht : q ≤ stdNormalCDF t) => (show p ≤ stdNormalCDF t by linarith)
  have hbddq : BddBelow Sq := hbddp.mono hsub
  have hclosed : IsClosed Sq := isClosed_le continuous_const hc
  have hmem : sInf Sq ∈ Sq := hclosed.csInf_mem hne hbddq
  set b := sInf Sq with hb
  have hqb : q ≤ stdNormalCDF b := hmem
  -- there is t < b with p < Φ t
  have hcb : ContinuousAt stdNormalCDF b := hc.continuousAt
  have hev : ∀ᶠ t in 𝓝 b, p < stdNormalCDF t :=
    hcb.eventually (lt_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have ht : p < stdNormalCDF (b - δ / 2) := by
    apply hball
    rw [Real.dist_eq]
    rw [abs_of_neg (by linarith)]
    linarith
  have hle : normalQuantile p ≤ b - δ / 2 := csInf_le hbddp ht.le
  show normalQuantile p < b
  linarith

/-- Key bound: the ratio with `d ≥ 0` is at most `ε`. -/
lemma aux_kz_ratio_le {ε d lam : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hd : 0 ≤ d) (hl : 0 < lam) :
    entropyRatio ε d lam ≤ ε := by
  unfold entropyRatio
  set t := 1 / lam with ht
  have htpos : 0 < t := by positivity
  have hεl : ε / lam = ε * t := by rw [ht]; field_simp
  rw [hεl]
  have hD : 0 < Real.exp t - 1 := by
    have := Real.add_one_lt_exp htpos.ne'
    linarith
  rw [div_le_iff₀ hD]
  -- convexity: exp (ε t) ≤ ε exp t + (1-ε)
  have hconv := convexOn_exp.2 (Set.mem_univ t) (Set.mem_univ 0) hε0.le (by linarith : (0:ℝ) ≤ 1 - ε)
    (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at hconv
  have h1 : Real.exp (ε * t - d) ≤ Real.exp (ε * t) := Real.exp_le_exp.2 (by linarith)
  nlinarith

lemma aux_kz_bdd {ε d : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hd : 0 ≤ d) :
    BddAbove (entropyRatio ε d '' Set.Ioi 0) := by
  refine ⟨ε, ?_⟩
  rintro x ⟨lam, hl, rfl⟩
  exact aux_kz_ratio_le hε0 hε1 hd hl

lemma aux_kz_ne (ε d : ℝ) : (entropyRatio ε d '' Set.Ioi 0).Nonempty :=
  ⟨_, 1, Set.mem_Ioi.2 one_pos, rfl⟩

lemma aux_kz_f_le {ε d : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hd : 0 ≤ d) :
    fEntropy ε d ≤ ε := by
  unfold fEntropy
  apply csSup_le (aux_kz_ne ε d)
  rintro x ⟨lam, hl, rfl⟩
  exact aux_kz_ratio_le hε0 hε1 hd hl

lemma aux_kz_f_pos {ε d : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hd : 0 ≤ d) :
    0 < fEntropy ε d := by
  have hl : 0 < ε / (d + 1) := by positivity
  have hmem : entropyRatio ε d (ε / (d + 1)) ∈ entropyRatio ε d '' Set.Ioi 0 := ⟨_, hl, rfl⟩
  have hle := le_csSup (aux_kz_bdd hε0 hε1 hd) hmem
  have hpos : 0 < entropyRatio ε d (ε / (d + 1)) := by
    unfold entropyRatio
    have e1 : ε / (ε / (d + 1)) - d = 1 := by field_simp; ring
    rw [e1]
    have hn : 0 < Real.exp 1 - 1 := by
      have := Real.add_one_lt_exp (one_ne_zero (α := ℝ))
      linarith
    have hpos' : 0 < 1 / (ε / (d + 1)) := by positivity
    have hd' : 0 < Real.exp (1 / (ε / (d + 1))) - 1 := by
      have := Real.add_one_lt_exp hpos'.ne'
      linarith
    exact div_pos hn hd'
  unfold fEntropy
  linarith


theorem aux_dc_K_pos (φ lam : ℝ) (hlam : 0 < lam) (hφ0 : 0 ≤ φ) :
    0 < (Real.exp (1 / lam) - 1) * φ + 1 := by
  have h1 : 0 ≤ Real.exp (1 / lam) - 1 := by
    have : 1 ≤ Real.exp (1 / lam) := Real.one_le_exp (by positivity)
    linarith
  have := mul_nonneg h1 hφ0
  linarith

theorem aux_dc_qpos {n : ℕ} (w : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (hΓ : Γ.PosDef) (hw : w ≠ 0) : 0 < quadForm Γ w := by
  have h := hΓ.dotProduct_mulVec_pos (x := w.ofLp) (by simpa using hw)
  unfold quadForm
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, star_trivial] at h
  refine lt_of_lt_of_eq h ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma aux_dc_strict : StrictMono stdNormalCDF := by
  have hmono : Monotone stdNormalCDF := monotone_cdf _
  intro y x hyx
  rcases (hmono hyx.le).lt_or_eq with h | h
  · exact h
  exfalso
  have h1 := (cdf (gaussianReal 0 1)).measure_Ioc y x
  rw [measure_cdf] at h1
  have h2 : cdf (gaussianReal 0 1) x - cdf (gaussianReal 0 1) y = 0 := by
    unfold stdNormalCDF at h; linarith
  rw [h2, ENNReal.ofReal_zero] at h1
  have h3 := gaussianReal_absolutelyContinuous' (0:ℝ) (v := 1) one_ne_zero h1
  rw [Real.volume_Ioc] at h3
  simp at h3
  linarith

lemma aux_dc_symm (t : ℝ) : stdNormalCDF (-t) = 1 - stdNormalCDF t := by
  unfold stdNormalCDF
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  rw [cdf_eq_real, cdf_eq_real]
  have hm : (gaussianReal 0 1).map (fun x : ℝ ↦ -x) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg]; simp
  conv_lhs => rw [← hm]
  rw [map_measureReal_apply (by fun_prop) measurableSet_Iic]
  have hpre : (fun x : ℝ ↦ -x) ⁻¹' Set.Iic (-t) = Set.Ici t := by
    ext x; simp
  rw [hpre, ← Set.compl_Iio, measureReal_compl measurableSet_Iio, probReal_univ,
    measureReal_congr Iio_ae_eq_Iic]

lemma aux_dc_quant {p x : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    x ≤ normalQuantile p ↔ stdNormalCDF x ≤ p := by
  have hc := aux_kz_cont
  have hne : {t : ℝ | p ≤ stdNormalCDF t}.Nonempty := by
    have ht : Tendsto stdNormalCDF atTop (𝓝 1) := tendsto_cdf_atTop _
    obtain ⟨t, ht⟩ := (ht.eventually (lt_mem_nhds hp1)).exists
    exact ⟨t, le_of_lt ht⟩
  have hbdd : BddBelow {t : ℝ | p ≤ stdNormalCDF t} := by
    have ht : Tendsto stdNormalCDF atBot (𝓝 0) := tendsto_cdf_atBot _
    obtain ⟨T, hT⟩ := eventually_atBot.1 (ht.eventually (gt_mem_nhds hp))
    refine ⟨T, fun t htS => ?_⟩
    by_contra hlt
    push_neg at hlt
    have := hT t hlt.le
    have h2 : p ≤ stdNormalCDF t := htS
    linarith
  constructor
  · intro hx
    by_contra hgt
    push_neg at hgt
    have hev : ∀ᶠ t in 𝓝 x, p < stdNormalCDF t := hc.continuousAt.eventually (lt_mem_nhds hgt)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    have ht : p < stdNormalCDF (x - δ / 2) := by
      apply hball
      rw [Real.dist_eq, abs_of_neg (by linarith)]
      linarith
    have hle : normalQuantile p ≤ x - δ / 2 := csInf_le hbdd ht.le
    linarith
  · intro hx
    apply le_csInf hne
    intro u hu
    have hu' : p ≤ stdNormalCDF u := hu
    exact aux_dc_strict.le_iff_le.1 (by linarith)

lemma aux_dc_cont_on {ε d a b : ℝ} (ha : 0 < a) :
    ContinuousOn (entropyRatio ε d) (Set.Icc a b) := by
  unfold entropyRatio
  apply ContinuousOn.div
  · apply ContinuousOn.sub _ continuousOn_const
    apply ContinuousOn.rexp
    apply ContinuousOn.sub _ continuousOn_const
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro x hx; exact (lt_of_lt_of_le ha hx.1).ne'
  · apply ContinuousOn.sub _ continuousOn_const
    apply ContinuousOn.rexp
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro x hx; exact (lt_of_lt_of_le ha hx.1).ne'
  · intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have h1 := one_div_pos.2 hx0
    have := Real.add_one_lt_exp h1.ne'
    linarith

/-- the supremum is attained -/
lemma aux_dc_attain {ε d : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hd : 0 < d) :
    ∃ lam > 0, fEntropy ε d ≤ entropyRatio ε d lam := by
  set l0 := ε / (d + 1) with hl0
  have hl0p : 0 < l0 := by positivity
  set c := entropyRatio ε d l0 with hc
  have hcpos : 0 < c := by
    rw [hc]
    unfold entropyRatio
    have e1 : ε / l0 - d = 1 := by rw [hl0]; field_simp; ring
    rw [e1]
    have hn : 0 < Real.exp 1 - 1 := by
      have := Real.add_one_lt_exp (one_ne_zero (α := ℝ))
      linarith
    have hpos' : 0 < 1 / l0 := by positivity
    have hd' : 0 < Real.exp (1 / l0) - 1 := by
      have := Real.add_one_lt_exp hpos'.ne'
      linarith
    exact div_pos hn hd'
  set T := max 1 (2 / (c * (1 - ε))) + 1 with hT
  have hT1 : 1 < T := by have := le_max_left 1 (2 / (c * (1 - ε))); linarith
  have hT2 : 2 / (c * (1 - ε)) < T := by have := le_max_right 1 (2 / (c * (1 - ε))); linarith
  set a := min l0 (1 / T) with ha
  have hapos : 0 < a := lt_min hl0p (by positivity)
  set b := ε / d with hb
  have hl0b : l0 ≤ b := by
    rw [hl0, hb]; apply div_le_div_of_nonneg_left hε0.le hd; linarith
  have hab : l0 ∈ Set.Icc a b := ⟨min_le_left _ _, hl0b⟩
  obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨l0, hab⟩ (aux_dc_cont_on (b := b) hapos)
  have hmpos : 0 < m := lt_of_lt_of_le hapos hm.1
  have hcm : c ≤ entropyRatio ε d m := hmax hab
  refine ⟨m, hmpos, ?_⟩
  unfold fEntropy
  apply csSup_le (aux_kz_ne ε d)
  rintro y ⟨lam, hl, rfl⟩
  have hl : 0 < lam := hl
  by_cases hin : lam ∈ Set.Icc a b
  · exact hmax hin
  · rw [Set.mem_Icc, not_and_or, not_le, not_le] at hin
    have htpos : 0 < 1 / lam := one_div_pos.2 hl
    have hD : 0 < Real.exp (1 / lam) - 1 := by
      have := Real.add_one_lt_exp htpos.ne'
      linarith
    rcases hin with hlt | hgt
    · -- small lam: ratio < c
      have hlt' : lam < 1 / T := lt_of_lt_of_le hlt (min_le_right _ _)
      have htT : T < 1 / lam := by
        rw [lt_div_iff₀ hl]; rw [lt_div_iff₀ (by linarith)] at hlt'; linarith
      set t := 1 / lam with ht
      have hεl : ε / lam = ε * t := by rw [ht]; field_simp
      suffices entropyRatio ε d lam < c by linarith
      unfold entropyRatio
      rw [hεl, div_lt_iff₀ hD]
      have h1 : Real.exp (ε * t - d) ≤ Real.exp (ε * t) := Real.exp_le_exp.2 (by linarith)
      have h2 : 2 ≤ Real.exp t := by
        have := Real.add_one_le_exp t
        linarith
      have h3 : (1 - ε) * t + 1 ≤ Real.exp ((1 - ε) * t) := Real.add_one_le_exp _
      have h4 : 2 / c < (1 - ε) * t := by
        rw [div_lt_iff₀ hcpos]
        have h1e : 0 < 1 - ε := by linarith
        rw [div_lt_iff₀ (mul_pos hcpos h1e)] at hT2
        nlinarith
      have h5 : 2 < c * Real.exp ((1 - ε) * t) := by
        rw [div_lt_iff₀ hcpos] at h4; nlinarith
      have h6 : Real.exp (ε * t) * Real.exp ((1 - ε) * t) = Real.exp t := by
        rw [← Real.exp_add]; ring_nf
      have hE : 0 < Real.exp (ε * t) := Real.exp_pos _
      nlinarith [mul_lt_mul_of_pos_left h5 hE]
    · -- large lam: ratio ≤ 0
      have : entropyRatio ε d lam ≤ 0 := by
        unfold entropyRatio
        apply div_nonpos_of_nonpos_of_nonneg _ hD.le
        have : ε / lam ≤ d := by
          rw [div_le_iff₀ hl]; rw [hb, div_lt_iff₀ hd] at hgt; linarith
        have := Real.exp_le_one_iff.2 (show ε / lam - d ≤ 0 by linarith)
        linarith
      linarith

lemma aux_dc_dual {d φ lam ε : ℝ} (hl : 0 < lam) (hφ : 0 ≤ φ) :
    dualValue d φ lam ≤ ε ↔ φ ≤ entropyRatio ε d lam := by
  have hK := aux_dc_K_pos φ lam hl hφ
  have hD : 0 < Real.exp (1 / lam) - 1 := by
    have h1 := one_div_pos.2 hl
    have := Real.add_one_lt_exp h1.ne'
    linarith
  unfold dualValue entropyRatio
  rw [le_div_iff₀ hD]
  have e1 : lam * d + lam * Real.log ((Real.exp (1 / lam) - 1) * φ + 1) ≤ ε ↔
      Real.log ((Real.exp (1 / lam) - 1) * φ + 1) ≤ ε / lam - d := by
    rw [le_sub_iff_add_le, le_div_iff₀ hl]
    constructor <;> intro h <;> linarith
  rw [e1, Real.log_le_iff_le_exp hK]
  constructor <;> intro h <;> linarith

theorem dci_core {n : ℕ} (xhat w : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (hΓ : Γ.PosDef) (hw : w ≠ 0) (ε d : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hd : 0 < d) (γ : ℝ) :
    (∃ lam > 0, dualValue d (gaussianTail xhat Γ w γ) lam ≤ ε) ↔
      kappaEntropy ε d * Real.sqrt (quadForm Γ w) - inner ℝ w xhat ≤ γ := by
  have hs : 0 < Real.sqrt (quadForm Γ w) := Real.sqrt_pos.2 (aux_dc_qpos w Γ hΓ hw)
  set s := Real.sqrt (quadForm Γ w)
  set t := (γ + inner ℝ w xhat) / s with ht
  have hφ : gaussianTail xhat Γ w γ = stdNormalCDF (-t) := by
    rw [aux_dc_symm]; rfl
  have hφ0 : 0 ≤ stdNormalCDF (-t) := cdf_nonneg _ _
  have hf0 := aux_kz_f_pos hε0 hε1 hd.le
  have hf1 := aux_kz_f_le hε0 hε1 hd.le
  have key : kappaEntropy ε d * s - inner ℝ w xhat ≤ γ ↔ stdNormalCDF (-t) ≤ fEntropy ε d := by
    rw [← aux_dc_quant hf0 (by linarith)]
    unfold kappaEntropy
    rw [ht, neg_le, le_div_iff₀ hs]
    constructor <;> intro h <;> linarith
  rw [key, hφ]
  constructor
  · rintro ⟨lam, hl, h⟩
    rw [aux_dc_dual hl hφ0] at h
    have hmem : entropyRatio ε d lam ∈ entropyRatio ε d '' Set.Ioi 0 := ⟨_, hl, rfl⟩
    exact h.trans (le_csSup (aux_kz_bdd hε0 hε1 hd.le) hmem)
  · intro h
    obtain ⟨lam, hl, hlam⟩ := aux_dc_attain hε0 hε1 hd
    exact ⟨lam, hl, (aux_dc_dual hl hφ0).2 (h.trans hlam)⟩

end WorstCaseVaR.Entropy

open WorstCaseVaR.Entropy


theorem solution {n : ℕ} (xhat w : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (hΓ : Γ.PosDef) (hw : w ≠ 0) (ε d : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hd : 0 < d) (γ : ℝ) :
    (∃ lam > 0, dualValue d (gaussianTail xhat Γ w γ) lam ≤ ε) ↔
      kappaEntropy ε d * Real.sqrt (quadForm Γ w) - inner ℝ w xhat ≤ γ := by
  exact dci_core xhat w Γ hΓ hw ε d hε0 hε1 hd γ

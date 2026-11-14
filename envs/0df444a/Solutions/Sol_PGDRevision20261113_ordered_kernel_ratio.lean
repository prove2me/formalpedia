-- Prove2me | solution 1 for PGDRevision20261113.ordered_kernel_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-11-13T09:54:49.871279+00:00
-- url     : https://prove2.me/submissions/be3cc882-b94a-4b74-9454-4469c521f597

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Definitions.Def_PGDRevision20261113_Geometry

open PGDRevision20261113
noncomputable section

private def skew (c t : ℝ) : ℝ :=
  (Real.rpow (1 - t) (-c) - Real.rpow (1 + t) (-c)) /
    (Real.rpow (1 - t) (-c) + Real.rpow (1 + t) (-c))

private lemma curvature_pos (c t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    0 < powerCurvature c t := by
  unfold powerCurvature
  exact div_pos (add_pos (Real.rpow_pos_of_pos (by linarith [ht.1]) _)
    (Real.rpow_pos_of_pos (by linarith [ht.2]) _)) (by norm_num)

private lemma skew_nonneg_mono (c₁ c₂ t : ℝ) (hc₁ : 0 ≤ c₁) (hc : c₁ ≤ c₂)
    (ht : t ∈ Set.Ico (0 : ℝ) 1) : 0 ≤ skew c₁ t ∧ skew c₁ t ≤ skew c₂ t := by
  have hminus : 0 < 1 - t := by linarith [ht.2]
  have hplus : 0 < 1 + t := by linarith [ht.1]
  have hbase : 1 ≤ (1 + t) / (1 - t) := by
    apply (le_div_iff₀ hminus).2
    linarith [ht.1]
  have hratio (c : ℝ) :
      Real.rpow (1 - t) (-c) / Real.rpow (1 + t) (-c) =
        Real.rpow ((1 + t) / (1 - t)) c := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_neg hminus.le, Real.rpow_neg hplus.le,
      inv_div_inv, Real.div_rpow hplus.le hminus.le]
  have ha₁ : 0 < Real.rpow (1 - t) (-c₁) := Real.rpow_pos_of_pos hminus _
  have hb₁ : 0 < Real.rpow (1 + t) (-c₁) := Real.rpow_pos_of_pos hplus _
  have ha₂ : 0 < Real.rpow (1 - t) (-c₂) := Real.rpow_pos_of_pos hminus _
  have hb₂ : 0 < Real.rpow (1 + t) (-c₂) := Real.rpow_pos_of_pos hplus _
  have hratio₁ : 1 ≤ Real.rpow (1 - t) (-c₁) / Real.rpow (1 + t) (-c₁) := by
    rw [hratio]
    simpa using Real.rpow_le_rpow_of_exponent_le hbase hc₁
  have hratios : Real.rpow (1 - t) (-c₁) / Real.rpow (1 + t) (-c₁) ≤
      Real.rpow (1 - t) (-c₂) / Real.rpow (1 + t) (-c₂) := by
    rw [hratio, hratio]
    exact Real.rpow_le_rpow_of_exponent_le hbase hc
  have horder := (le_div_iff₀ hb₁).mp hratio₁
  have hcross := (div_le_div_iff₀ hb₁ hb₂).mp hratios
  constructor
  · exact div_nonneg (by linarith) (by linarith)
  · unfold skew
    apply (div_le_div_iff₀ (add_pos ha₁ hb₁) (add_pos ha₂ hb₂)).2
    nlinarith only [hcross]

private lemma curvature_hasDerivAt (c t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    HasDerivAt (powerCurvature c)
      (powerCurvature c t * (c * (t + skew c t)) / (1 - t ^ 2)) t := by
  have hplus : 0 < 1 + t := by linarith [ht.1]
  have hminus : 0 < 1 - t := by linarith [ht.2]
  have hp := ((hasDerivAt_id t).const_add 1).rpow_const
    (Or.inl (ne_of_gt hplus) : 1 + t ≠ 0 ∨ 1 ≤ -c)
  have hm := ((hasDerivAt_id t).const_sub 1).rpow_const
    (Or.inl (ne_of_gt hminus) : 1 - t ≠ 0 ∨ 1 ≤ -c)
  have hsum : Real.rpow (1 - t) (-c) + Real.rpow (1 + t) (-c) ≠ 0 :=
    ne_of_gt (add_pos (Real.rpow_pos_of_pos hminus _) (Real.rpow_pos_of_pos hplus _))
  have hden : 1 - t ^ 2 ≠ 0 := ne_of_gt (by nlinarith [ht.1, ht.2])
  convert (hp.add hm).div_const 2 using 1 <;> try rfl
  unfold powerCurvature skew
  simp only [id_eq, Real.rpow_eq_pow] at hsum ⊢
  rw [Real.rpow_sub_one (ne_of_gt hplus), Real.rpow_sub_one (ne_of_gt hminus)]
  field_simp [hsum, hden, ne_of_gt hplus, ne_of_gt hminus]
  <;> ring

private lemma ratio_hasDerivAt (c₁ c₂ t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    HasDerivAt (fun t => powerCurvature c₂ t / powerCurvature c₁ t)
      ((powerCurvature c₂ t / powerCurvature c₁ t) *
        (c₂ * (t + skew c₂ t) - c₁ * (t + skew c₁ t)) / (1 - t ^ 2)) t := by
  have hk : powerCurvature c₁ t ≠ 0 := ne_of_gt (curvature_pos c₁ t ht)
  have hd : 1 - t ^ 2 ≠ 0 := ne_of_gt (by nlinarith [ht.1, ht.2])
  convert (curvature_hasDerivAt c₂ t ht).div (curvature_hasDerivAt c₁ t ht) hk using 1
    <;> try rfl
  field_simp [hk, hd]
  <;> ring

private lemma power_ratio_mono (c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hc : c₁ < c₂) :
    StrictMonoOn (fun t : ℝ => powerCurvature c₂ t / powerCurvature c₁ t)
      (Set.Ico (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ico 0 1)
  · intro t ht
    exact (ratio_hasDerivAt c₁ c₂ t ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ico] at ht
    have htco : t ∈ Set.Ico (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    rw [(ratio_hasDerivAt c₁ c₂ t htco).deriv]
    have hskew := skew_nonneg_mono c₁ c₂ t hc₁ hc.le htco
    have hprod : c₁ * (t + skew c₁ t) < c₂ * (t + skew c₂ t) := by
      calc
        c₁ * (t + skew c₁ t) < c₂ * (t + skew c₁ t) :=
          mul_lt_mul_of_pos_right hc (by linarith [ht.1, hskew.1])
        _ ≤ c₂ * (t + skew c₂ t) :=
          mul_le_mul_of_nonneg_left (by linarith [hskew.2]) (by linarith)
    exact div_pos (mul_pos (div_pos (curvature_pos c₂ t htco) (curvature_pos c₁ t htco))
      (sub_pos.mpr hprod)) (by nlinarith [ht.1, ht.2])

private lemma power_abs (c t : ℝ) : powerCurvature c |t| = powerCurvature c t := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht)]
    simp only [powerCurvature, sub_eq_add_neg, neg_neg, add_comm]

theorem solution : OrderedKernelRatioClaim := by
  intro G hG c1 c2 p1 p2 hc1 hc hp1 hp2 x hx y hy hxy
  rcases hG with ⟨hlam, hA, hbound, hpos, hfamily⟩
  cases hf : G.family with
  | interval beta =>
    have hxd : x ∈ Set.Ioo (-1 : ℝ) 1 := by simpa [geometryDomain, hf] using hx
    have hyd : y ∈ Set.Ioo (-1 : ℝ) 1 := by simpa [geometryDomain, hf] using hy
    have hxabs : |x| ∈ Set.Ico (0 : ℝ) 1 := ⟨abs_nonneg _, abs_lt.mpr hxd⟩
    have hyabs : |y| ∈ Set.Ico (0 : ℝ) 1 := ⟨abs_nonneg _, abs_lt.mpr hyd⟩
    have hxyabs : |x| < |y| := by simpa [geometryFeature, hf] using hxy
    have hr := power_ratio_mono c1 c2 hc1 hc hxabs hyabs hxyabs
    dsimp only at hr
    simp only [power_abs] at hr
    simpa only [geometryKernel, hf, div_mul_div_comm] using
      mul_lt_mul_of_pos_left hr (div_pos hp2 hp1)
  | realLine =>
    simp only [hf] at hfamily
    rcases hfamily with ⟨hA', hb', hb0, hb1, hbm, hbp, hbt⟩
    have hb (t : ℝ) : 0 < G.b t := by
      by_cases ht : t = 0
      · subst t
        rw [hb0]
        norm_num
      · linarith [hb1 t ht]
    have hbx := hb x
    have hby := hb y
    have hlog : Real.log (G.b x) < Real.log (G.b y) := by
      simpa [geometryFeature, hf] using hxy
    have hlt : G.b x < G.b y := by
      have he := Real.exp_lt_exp.mpr hlog
      simpa only [Real.exp_log hbx, Real.exp_log hby] using he
    have hratio : Real.rpow (G.b x) c2 / Real.rpow (G.b x) c1 <
        Real.rpow (G.b y) c2 / Real.rpow (G.b y) c1 := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_sub hbx, ← Real.rpow_sub hby]
      exact Real.rpow_lt_rpow hbx.le hlt (sub_pos.mpr hc)
    simpa only [geometryKernel, hf, div_mul_div_comm] using
      mul_lt_mul_of_pos_left hratio (div_pos hp2 hp1)

-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P11.scalarThermalAsymptotics
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T12:39:13.680489+00:00
-- url     : https://prove2.me/submissions/01a141fb-73a9-42d7-b906-20167bd11d4a

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P11

namespace G59P

noncomputable def g (v : ℝ) : ℝ := (v + 1) * Real.log (v + 1) - v * Real.log v

lemma g_zero : g 0 = 0 := by simp [g]

lemma g_cont : ContinuousOn g (Set.Ici 0) := by
  have h1 : ContinuousOn (fun v : ℝ => (v + 1) * Real.log (v + 1)) (Set.Ici 0) := by
    apply ContinuousOn.mul (continuousOn_id.add continuousOn_const)
    apply ContinuousOn.log (continuousOn_id.add continuousOn_const)
    intro x hx; have : (0:ℝ) ≤ x := hx; exact ne_of_gt (by simp; linarith)
  exact h1.sub Real.continuous_mul_log.continuousOn

lemma g_hasDeriv {v : ℝ} (hv : 0 < v) :
    HasDerivAt g (Real.log (v + 1) - Real.log v) v := by
  have h1 : HasDerivAt (fun v : ℝ => v + 1) 1 v := (hasDerivAt_id v).add_const 1
  have h2 := h1.mul (h1.log (by linarith))
  have h3 := (hasDerivAt_id v).mul (Real.hasDerivAt_log hv.ne')
  have := h2.sub h3
  refine this.congr_deriv ?_
  simp only [id, one_mul]
  field_simp
  ring

lemma g_strictMono : StrictMonoOn g (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) g_cont
  intro x hx
  rw [interior_Ici] at hx
  rw [(g_hasDeriv hx).deriv]
  have := Real.log_lt_log hx (by linarith : x < x + 1)
  linarith

lemma g_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ g v := by
  rw [← g_zero]; exact g_strictMono.monotoneOn (Set.mem_Ici.2 le_rfl) hv hv

lemma g_ge_log {v : ℝ} (hv : 0 ≤ v) : Real.log (v + 1) ≤ g v := by
  unfold g
  have hl : Real.log v ≤ Real.log (v + 1) := by
    rcases hv.eq_or_lt with h | h
    · subst h; simp
    · exact Real.log_le_log h (by linarith)
  nlinarith

/-- 2 log y ≤ y - 1/y for y ≥ 1. -/
lemma two_log_le {y : ℝ} (hy : 1 ≤ y) : 2 * Real.log y ≤ y - 1 / y := by
  let ψ : ℝ → ℝ := fun t => t - t⁻¹ - 2 * Real.log t
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt ψ (1 - (-(x ^ 2)⁻¹) - 2 * x⁻¹) x := by
    intro x hx0
    have := ((hasDerivAt_id' x).sub (hasDerivAt_inv hx0.ne')).sub
      ((Real.hasDerivAt_log hx0.ne').const_mul 2)
    exact this
  have hmono : MonotoneOn ψ (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · intro x hx
      have : (1:ℝ) ≤ x := hx
      exact (hd x (by linarith)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have : (1:ℝ) < x := hx
      exact (hd x (by linarith)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have : (1:ℝ) < x := hx
      rw [(hd x (by linarith)).deriv]
      have : 1 - (-(x ^ 2)⁻¹) - 2 * x⁻¹ = (1 - x⁻¹) ^ 2 := by field_simp; ring
      rw [this]; positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy) hy
  simp only [ψ, inv_one, Real.log_one] at this
  rw [one_div]
  linarith

lemma key {N : ℝ} (hN : 0 < N) :
    (Real.log (N + 1) - Real.log N) ^ 2 ≤ 1 / N - 1 / (N + 1) := by
  set z := (N + 1) / N with hz
  have hz1 : 1 ≤ z := by rw [hz, le_div_iff₀ hN]; linarith
  set y := Real.sqrt z with hy
  have hy1 : 1 ≤ y := by rw [hy]; exact Real.one_le_sqrt.2 hz1
  have hy0 : 0 < y := by linarith
  have hyy : y ^ 2 = z := Real.sq_sqrt (by linarith)
  have hd : Real.log (N + 1) - Real.log N = 2 * Real.log y := by
    rw [hy, Real.log_sqrt (by linarith), hz, Real.log_div (by linarith) hN.ne']
    ring
  have hle := two_log_le hy1
  have hd0 : 0 ≤ Real.log (N + 1) - Real.log N := by
    have := Real.log_le_log hN (by linarith : N ≤ N + 1); linarith
  have hb : y - 1 / y = (1 / N) / y := by
    field_simp
    rw [hyy, hz]; field_simp; ring
  rw [hd] at hd0 ⊢
  have h2 : (2 * Real.log y) ^ 2 ≤ ((1 / N) / y) ^ 2 :=
    pow_le_pow_left₀ hd0 (hb ▸ hle) 2
  have h3 : ((1 / N) / y) ^ 2 = 1 / N - 1 / (N + 1) := by
    rw [div_pow, hyy, hz]; field_simp; ring
  linarith

noncomputable def h (v : ℝ) : ℝ := Real.exp (g v)

noncomputable def k (v : ℝ) : ℝ := (Real.log (v + 1) - Real.log v) * Real.exp (g v)

lemma h_hasDeriv {v : ℝ} (hv : 0 < v) : HasDerivAt h (k v) v := by
  have := (g_hasDeriv hv).exp
  unfold h k; convert this using 1; ring

lemma k_hasDeriv {v : ℝ} (hv : 0 < v) :
    HasDerivAt k ((1 / (v + 1) - 1 / v) * Real.exp (g v) +
      (Real.log (v + 1) - Real.log v) * ((Real.log (v + 1) - Real.log v) * Real.exp (g v))) v := by
  have h1 : HasDerivAt (fun v : ℝ => v + 1) 1 v := (hasDerivAt_id v).add_const 1
  have a := (h1.log (by linarith)).sub (Real.hasDerivAt_log hv.ne')
  have b := (g_hasDeriv hv).exp
  have := a.mul b
  refine this.congr_deriv ?_
  simp only [Pi.sub_apply]
  field_simp

lemma h_concave : ConcaveOn ℝ (Set.Ici 0) h := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0)
  · exact Real.continuous_exp.comp_continuousOn g_cont
  · rw [interior_Ici]; intro x hx
    exact (h_hasDeriv hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    have hk : AntitoneOn k (Set.Ioi 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
      · intro x hx; exact (k_hasDeriv hx).continuousAt.continuousWithinAt
      · rw [interior_Ioi]; intro x hx
        exact (k_hasDeriv hx).differentiableAt.differentiableWithinAt
      · rw [interior_Ioi]; intro x hx
        rw [(k_hasDeriv hx).deriv]
        have := key hx
        have he := Real.exp_pos (g x)
        have : ((1 / (x + 1) - 1 / x) + (Real.log (x + 1) - Real.log x) ^ 2) * Real.exp (g x) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) he.le
        nlinarith
    intro a ha b hb hab
    rw [(h_hasDeriv ha).deriv, (h_hasDeriv hb).deriv]
    exact hk ha hb hab

end G59P

noncomputable section

open Filter
open scoped Topology
open QAlgorithms.Papers.Independent.Claimed50.P11
open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)
open QAlgorithms.Papers.Independent.Dependency50.P39 (attenuatorMatrix)

lemma g59_te : thermalEntropy = G59P.g := rfl

lemma g59_spec {s : ℝ} (hs : 0 ≤ s) :
    ∃ N, 0 ≤ N ∧ G59P.g N = s ∧ thermalEntropyInverse s = N := by
  rcases hs.eq_or_lt with h0 | hpos
  · subst h0; exact ⟨0, le_rfl, G59P.g_zero, by simp [thermalEntropyInverse]⟩
  have he : 0 ≤ Real.exp s := (Real.exp_pos s).le
  have hmem : s ∈ Set.Icc (G59P.g 0) (G59P.g (Real.exp s)) := by
    refine ⟨by rw [G59P.g_zero]; exact hs, ?_⟩
    have h1 := G59P.g_ge_log he
    have h2 : s ≤ Real.log (Real.exp s + 1) := by
      rw [← Real.log_exp s]
      exact Real.log_le_log (Real.exp_pos _) (by rw [Real.log_exp]; linarith)
    linarith
  obtain ⟨N, ⟨hN0, -⟩, hgN⟩ :=
    intermediate_value_Icc he (G59P.g_cont.mono Set.Icc_subset_Ici_self) hmem
  refine ⟨N, hN0, hgN, ?_⟩
  unfold thermalEntropyInverse
  rw [if_neg (not_le.2 hpos), g59_te]
  apply IsLeast.csInf_eq
  refine ⟨⟨hN0, hgN.ge⟩, ?_⟩
  rintro M ⟨hM0, hM⟩
  exact (G59P.g_strictMono.le_iff_le hN0 hM0).1 (hgN ▸ hM)

/-- for `x ≥ 1`, `f x` is the nonnegative `N` with `exp (g N) = x`. -/
lemma g59_f {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ entropyPowerPhoton x ∧ G59P.h (entropyPowerPhoton x) = x := by
  obtain ⟨N, hN0, hgN, hf⟩ := g59_spec (Real.log_nonneg hx)
  unfold entropyPowerPhoton
  rw [hf]
  refine ⟨hN0, ?_⟩
  unfold G59P.h; rw [hgN, Real.exp_log (by linarith)]

lemma g59_fh {N : ℝ} (hN : 0 ≤ N) : entropyPowerPhoton (G59P.h N) = N := by
  obtain ⟨M, hM0, hgM, hf⟩ := g59_spec (G59P.g_nonneg hN)
  unfold entropyPowerPhoton G59P.h
  rw [Real.log_exp, hf]
  exact G59P.g_strictMono.injOn hM0 hN hgM

lemma g59_h_le_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : G59P.h a ≤ G59P.h b ↔ a ≤ b := by
  unfold G59P.h
  rw [Real.exp_le_exp]
  exact G59P.g_strictMono.le_iff_le ha hb

lemma g59_h_ge_one {a : ℝ} (ha : 0 ≤ a) : 1 ≤ G59P.h a := by
  unfold G59P.h; exact Real.one_le_exp (G59P.g_nonneg ha)

lemma g59_mono : MonotoneOn entropyPowerPhoton (Set.Ici 1) := by
  intro x hx y hy hxy
  obtain ⟨hx0, hx1⟩ := g59_f hx
  obtain ⟨hy0, hy1⟩ := g59_f hy
  rw [← g59_h_le_iff hx0 hy0, hx1, hy1]; exact hxy

lemma g59_convex : ConvexOn ℝ (Set.Ici 1) entropyPowerPhoton := by
  refine ⟨convex_Ici 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : (1:ℝ) ≤ x := hx
  have hy' : (1:ℝ) ≤ y := hy
  have hz : (1:ℝ) ≤ a • x + b • y := by
    simp only [smul_eq_mul]; nlinarith
  obtain ⟨hx0, hx1⟩ := g59_f hx'
  obtain ⟨hy0, hy1⟩ := g59_f hy'
  obtain ⟨hz0, hz1⟩ := g59_f hz
  have hc := G59P.h_concave.2 (Set.mem_Ici.2 hx0) (Set.mem_Ici.2 hy0) ha hb hab
  rw [hx1, hy1] at hc
  have hm : 0 ≤ a • entropyPowerPhoton x + b • entropyPowerPhoton y := by
    simp only [smul_eq_mul]; positivity
  rw [← g59_h_le_iff hz0 hm, hz1]
  exact hc


lemma g59_logs {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 2) :
    |Real.log (1 + t) - Real.log (1 - t) - 2 * t| ≤ 4 * t ^ 3 ∧
    |Real.log (1 - t ^ 2)| ≤ 4 / 3 * t ^ 2 := by
  have hta : |t| = t := abs_of_pos ht0
  have htn : |-t| = t := by rw [abs_neg, hta]
  have e1 := Real.abs_log_sub_add_sum_range_le (x := -t) (by rw [htn]; linarith) 2
  have e2 := Real.abs_log_sub_add_sum_range_le (x := t) (by rw [hta]; linarith) 2
  have e3 := Real.abs_log_sub_add_sum_range_le (x := t ^ 2)
    (by rw [abs_of_nonneg (by positivity)]; nlinarith) 0
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, htn, hta, sub_neg_eq_add] at e1 e2 e3
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ 2)] at e3
  norm_num at e1 e2 e3
  have hd : t ^ 3 / (1 - t) ≤ 2 * t ^ 3 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [pow_pos ht0 3]
  have hd2 : t ^ 2 / (1 - t ^ 2) ≤ 4 / 3 * t ^ 2 := by
    have h14 : t ^ 2 ≤ 1 / 4 := by nlinarith
    rw [div_le_iff₀ (by nlinarith)]; nlinarith [mul_le_mul_of_nonneg_left h14 (sq_nonneg t)]
  constructor
  · have := abs_sub (-t + t ^ 2 / 2 + Real.log (1 + t)) (t + t ^ 2 / 2 + Real.log (1 - t))
    have hh : (-t + t ^ 2 / 2 + Real.log (1 + t)) - (t + t ^ 2 / 2 + Real.log (1 - t)) =
      Real.log (1 + t) - Real.log (1 - t) - 2 * t := by ring
    rw [hh] at this
    have e1' : |-t + t ^ 2 / 2 + Real.log (1 + t)| ≤ t ^ 3 / (1 - t) := by
      convert e1 using 2
    linarith
  · linarith

lemma g59_asym1 {x : ℝ} (hx : 1 ≤ x) :
    |G59P.g (x - 1 / 2) - Real.log (Real.exp 1 * x)| ≤ 1 / x ^ 2 := by
  have hx0 : 0 < x := by linarith
  set t := 1 / (2 * x) with htdef
  have ht0 : 0 < t := by positivity
  have ht : t ≤ 1 / 2 := by rw [htdef, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  obtain ⟨h1, h2⟩ := g59_logs ht0 ht
  have hp : 0 < 1 + t := by linarith
  have hm : 0 < 1 - t := by linarith
  have hxp : x - 1 / 2 + 1 = x * (1 + t) := by rw [htdef]; field_simp; ring
  have hxm : x - 1 / 2 = x * (1 - t) := by rw [htdef]; field_simp
  have hl : Real.log (1 - t ^ 2) = Real.log (1 + t) + Real.log (1 - t) := by
    rw [← Real.log_mul hp.ne' hm.ne']; ring_nf
  have key : G59P.g (x - 1 / 2) - Real.log (Real.exp 1 * x) =
      x * (Real.log (1 + t) - Real.log (1 - t) - 2 * t) + Real.log (1 - t ^ 2) / 2 := by
    unfold G59P.g
    rw [hxp, hxm, Real.log_mul hx0.ne' hp.ne', Real.log_mul hx0.ne' hm.ne',
      Real.log_mul (Real.exp_pos 1).ne' hx0.ne', Real.log_exp, hl]
    have : x * t = 1 / 2 := by rw [htdef]; field_simp
    linear_combination (2 * Real.log x + Real.log (1 + t) + Real.log (1 - t) + 2) * this
  rw [key]
  have hxt : x * t = 1 / 2 := by rw [htdef]; field_simp
  have h3 : |x * (Real.log (1 + t) - Real.log (1 - t) - 2 * t)| ≤ 2 * t ^ 2 := by
    rw [abs_mul, abs_of_pos hx0]
    calc x * |Real.log (1 + t) - Real.log (1 - t) - 2 * t| ≤ x * (4 * t ^ 3) :=
          mul_le_mul_of_nonneg_left h1 hx0.le
      _ = 2 * t ^ 2 := by rw [show x * (4 * t ^ 3) = 4 * (x * t) * t ^ 2 by ring, hxt]; ring
  have h4 : |Real.log (1 - t ^ 2) / 2| ≤ 2 / 3 * t ^ 2 := by
    rw [abs_div, abs_two]; linarith
  have h5 : t ^ 2 = 1 / (4 * x ^ 2) := by rw [htdef]; field_simp; ring
  have h6 : 3 * (1 / (4 * x ^ 2)) ≤ 1 / x ^ 2 := by
    rw [show 3 * (1 / (4 * x ^ 2)) = (3 / 4) * (1 / x ^ 2) by field_simp]
    have : 0 < 1 / x ^ 2 := by positivity
    linarith
  calc _ ≤ |x * (Real.log (1 + t) - Real.log (1 - t) - 2 * t)| + |Real.log (1 - t ^ 2) / 2| :=
        abs_add_le _ _
    _ ≤ 2 * t ^ 2 + 2 / 3 * t ^ 2 := add_le_add h3 h4
    _ ≤ 3 * t ^ 2 := by nlinarith [sq_nonneg t]
    _ ≤ 1 / x ^ 2 := by rw [h5]; exact h6

lemma g59_asym2 {N : ℝ} (hN : 1 ≤ N) :
    |Real.exp (G59P.g N) - Real.exp 1 * (N + 1 / 2)| ≤ 6 / N := by
  have hN0 : 0 < N := by linarith
  set x := N + 1 / 2 with hx
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have a := g59_asym1 hx1
  rw [show x - 1 / 2 = N by rw [hx]; ring] at a
  set u := G59P.g N - Real.log (Real.exp 1 * x) with hu
  have hex : 0 < Real.exp 1 * x := by positivity
  have hg : Real.exp (G59P.g N) = Real.exp 1 * x * Real.exp u := by
    rw [hu, Real.exp_sub, Real.exp_log hex]; field_simp
  have hx2 : 1 / x ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have hu1 : |u| ≤ 1 := le_trans a hx2
  have he := Real.abs_exp_sub_one_le hu1
  rw [hg, show Real.exp 1 * x * Real.exp u - Real.exp 1 * x = Real.exp 1 * x * (Real.exp u - 1) by ring,
    abs_mul, abs_of_pos hex]
  have e3 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
  calc Real.exp 1 * x * |Real.exp u - 1| ≤ Real.exp 1 * x * (2 * (1 / x ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hex.le; linarith
    _ = 2 * Real.exp 1 / x := by field_simp
    _ ≤ 6 / x := by apply div_le_div_of_nonneg_right _ hx0.le; linarith
    _ ≤ 6 / N := by
        rw [div_le_div_iff₀ hx0 hN0, hx]; linarith

lemma g59_h_one : G59P.h 1 = 4 := by
  unfold G59P.h G59P.g
  rw [show (1:ℝ) + 1 = 2 by norm_num, Real.log_one, mul_zero, sub_zero,
    show (2:ℝ) * Real.log 2 = Real.log (2 ^ 2) by rw [Real.log_pow]; norm_num,
    Real.exp_log (by norm_num)]
  norm_num

lemma g59_asym3 {x : ℝ} (hx : 4 ≤ x) :
    |entropyPowerPhoton x - (x / Real.exp 1 - 1 / 2)| ≤ 40 / x := by
  obtain ⟨hN0, hNx⟩ := g59_f (by linarith : (1:ℝ) ≤ x)
  set N := entropyPowerPhoton x
  have hN1 : 1 ≤ N := by
    rw [← g59_h_le_iff zero_le_one hN0, g59_h_one, hNx]; exact hx
  have a := g59_asym2 hN1
  have hhx : Real.exp (G59P.g N) = x := hNx
  rw [hhx] at a
  have e3 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
  have e2 : 2 < Real.exp 1 := by have := Real.exp_one_gt_d9; norm_num at this ⊢; linarith
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hN0' : 0 < N := by linarith
  have hx0 : 0 < x := by linarith
  have heq : N - (x / Real.exp 1 - 1 / 2) = -(x - Real.exp 1 * (N + 1 / 2)) / Real.exp 1 := by
    field_simp; ring
  rw [heq, abs_div, abs_neg, abs_of_pos he0]
  have hxN : x ≤ 11 * N := by
    have h1 := (abs_le.1 a).2
    have h2 : 6 / N ≤ 6 := by rw [div_le_iff₀ hN0']; linarith
    have h3 : Real.exp 1 * (N + 1 / 2) ≤ 3 * (N + 1 / 2) :=
      mul_le_mul_of_nonneg_right e3.le (by linarith)
    linarith
  have h6 : |x - Real.exp 1 * (N + 1 / 2)| ≤ 6 / N := a
  have h7 : |x - Real.exp 1 * (N + 1 / 2)| / Real.exp 1 ≤ (6 / N) / 2 := by
    rw [div_le_div_iff₀ he0 (by norm_num)]
    have : 0 ≤ 6 / N := by positivity
    nlinarith
  have h8 : (6 / N) / 2 ≤ 40 / x := by
    rw [div_div, div_le_div_iff₀ (by positivity) hx0]; nlinarith
  linarith

theorem solution :
    (∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 ≤ x0 ∧ ∀ x : ℝ, x0 ≤ x →
      |thermalEntropy (x - 1 / 2) - Real.log (Real.exp 1 * x)| ≤ C / x ^ 2) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ N0 : ℝ, 1 ≤ N0 ∧ ∀ N : ℝ, N0 ≤ N →
      |Real.exp (thermalEntropy N) - Real.exp 1 * (N + 1 / 2)| ≤ C / N) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 ≤ x0 ∧ ∀ x : ℝ, x0 ≤ x →
      |entropyPowerPhoton x - (x / Real.exp 1 - 1 / 2)| ≤ C / x) := by
  refine ⟨⟨1, one_pos, 1, le_rfl, fun x hx => g59_asym1 hx⟩,
    ⟨6, by norm_num, 1, le_rfl, fun N hN => g59_asym2 hN⟩,
    ⟨40, by norm_num, 4, by norm_num, fun x hx => g59_asym3 hx⟩⟩

end

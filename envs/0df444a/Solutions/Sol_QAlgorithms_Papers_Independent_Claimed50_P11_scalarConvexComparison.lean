-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P11.scalarConvexComparison
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T12:36:12.130979+00:00
-- url     : https://prove2.me/submissions/89ab6f7b-4fd0-4428-bc22-617701f85d4f

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

theorem solution :
    MonotoneOn entropyPowerPhoton (Set.Ici 1) ∧
    ConvexOn ℝ (Set.Ici 1) entropyPowerPhoton ∧
    (∀ lambda NA NB : ℝ, 0 ≤ lambda → lambda ≤ 1 → 0 ≤ NA → 0 ≤ NB →
      entropyPowerPhoton
        (lambda * Real.exp (thermalEntropy NA) +
          (1 - lambda) * Real.exp (thermalEntropy NB)) ≤
        lambda * NA + (1 - lambda) * NB) := by
  refine ⟨g59_mono, g59_convex, ?_⟩
  intro lambda NA NB h0 h1 hA hB
  have := g59_convex.2 (Set.mem_Ici.2 (g59_h_ge_one hA)) (Set.mem_Ici.2 (g59_h_ge_one hB))
    h0 (by linarith : 0 ≤ 1 - lambda) (by ring)
  simp only [smul_eq_mul, g59_fh hA, g59_fh hB] at this
  exact this

end

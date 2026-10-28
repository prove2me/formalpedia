-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P06.g_difference_monotone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:31:18.788551+00:00
-- url     : https://prove2.me/submissions/e8b64b8d-c2bc-480c-b713-b8acbd90cfc8

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P06

-- ===== P06A =====

open Real Set
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

namespace X4P06

lemma g_eq (x : ℝ) : g x = (x + 1) * log (x + 1) - x * log x := rfl

lemma g_cont : Continuous g := by
  have := Real.continuous_mul_log
  exact (this.comp (continuous_id.add continuous_const)).sub this

lemma g_zero : g 0 = 0 := by simp [g_eq]

lemma g_hasDeriv {x : ℝ} (hx : 0 < x) : HasDerivAt g (log (x + 1) - log x) x := by
  have h1 : HasDerivAt (fun y => (y + 1) * log (y + 1)) (log (x + 1) + 1) x :=
    (hasDerivAt_mul_log (by linarith : x + 1 ≠ 0)).comp_add_const x 1
  have h2 := hasDerivAt_mul_log hx.ne'
  rw [show log (x + 1) - log x = (log (x + 1) + 1) - (log x + 1) by ring]
  exact h1.sub h2

lemma g_deriv {x : ℝ} (hx : 0 < x) : deriv g x = log (x + 1) - log x := (g_hasDeriv hx).deriv

lemma g_deriv_pos {x : ℝ} (hx : 0 < x) : 0 < log (x + 1) - log x := by
  have := Real.log_lt_log hx (by linarith : x < x + 1); linarith

lemma g_strictMono : StrictMonoOn g (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) g_cont.continuousOn fun x hx => ?_
  rw [interior_Ici] at hx
  rw [g_deriv hx]; exact g_deriv_pos hx

lemma g_mono : MonotoneOn g (Ici 0) := g_strictMono.monotoneOn

lemma g_nonneg {N : ℝ} (hN : 0 ≤ N) : 0 ≤ g N := by
  have := g_mono (Set.mem_Ici.mpr (le_refl (0:ℝ))) (hN : N ∈ Ici 0) hN; rwa [g_zero] at this

lemma g_concave : ConcaveOn ℝ (Ici 0) g := by
  refine AntitoneOn.concaveOn_of_deriv (convex_Ici 0) g_cont.continuousOn ?_ ?_
  · rw [interior_Ici]; intro x hx; exact (g_hasDeriv hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro x hx y hy hxy
    simp only [mem_Ioi] at hx hy
    rw [g_deriv hx, g_deriv hy]
    rw [← Real.log_div (by linarith) hx.ne', ← Real.log_div (by linarith) hy.ne']
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ hy hx]; nlinarith

lemma g_ge_log {x : ℝ} (hx : 0 ≤ x) : log (x + 1) ≤ g x := by
  rw [g_eq]
  rcases hx.eq_or_lt with rfl | hx
  · simp
  have : log x ≤ log (x + 1) := Real.log_le_log hx (by linarith)
  nlinarith

lemma g_unbounded (s : ℝ) : ∃ N, 0 ≤ N ∧ s ≤ g N := by
  refine ⟨max 0 (exp s), le_max_left _ _, ?_⟩
  refine le_trans ?_ (g_ge_log (le_max_left _ _))
  calc s = log (exp s) := (log_exp s).symm
    _ ≤ log (max 0 (exp s) + 1) := Real.log_le_log (exp_pos s) (by
        have := le_max_right 0 (exp s); linarith)

end X4P06

-- ===== P06B =====

open Real Set
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

namespace X4P06

lemma surj {s : ℝ} (hs : 0 ≤ s) : ∃ N, 0 ≤ N ∧ g N = s := by
  obtain ⟨M, hM, hsM⟩ := g_unbounded s
  have := intermediate_value_Icc hM g_cont.continuousOn (show s ∈ Icc (g 0) (g M) from
    ⟨by rw [g_zero]; exact hs, hsM⟩)
  obtain ⟨N, ⟨hN, -⟩, hgN⟩ := this
  exact ⟨N, hN, hgN⟩

lemma inv_g {N : ℝ} (hN : 0 ≤ N) : thermalEntropyInverse (g N) = N := by
  unfold thermalEntropyInverse
  split_ifs with h
  · have h0 : g N = 0 := le_antisymm h (g_nonneg hN)
    by_contra hne
    have := g_strictMono (Set.mem_Ici.mpr (le_refl (0:ℝ))) (Set.mem_Ici.mpr hN)
      (lt_of_le_of_ne hN hne)
    rw [g_zero, h0] at this; exact lt_irrefl _ this
  · have : {M : ℝ | 0 ≤ M ∧ g N ≤ QAlgorithms.Papers.Independent.Information100.P49.thermalEntropy M}
        = Ici N := by
      ext M
      simp only [Set.mem_ofPred_eq, mem_Ici]
      constructor
      · rintro ⟨hM, h⟩
        exact (g_strictMono.le_iff_le (Set.mem_Ici.mpr hN) (Set.mem_Ici.mpr hM)).mp h
      · intro h
        exact ⟨hN.trans h, g_mono (Set.mem_Ici.mpr hN) (Set.mem_Ici.mpr (hN.trans h)) h⟩
    rw [this, csInf_Ici]

lemma g_inv {s : ℝ} (hs : 0 ≤ s) : g (thermalEntropyInverse s) = s := by
  obtain ⟨N, hN, rfl⟩ := surj hs
  rw [inv_g hN]

lemma inv_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ thermalEntropyInverse s := by
  obtain ⟨N, hN, rfl⟩ := surj hs
  rw [inv_g hN]; exact hN

lemma inv_mono : MonotoneOn thermalEntropyInverse (Ici 0) := by
  intro s hs t ht hst
  obtain ⟨N, hN, rfl⟩ := surj hs
  obtain ⟨M, hM, rfl⟩ := surj ht
  rw [inv_g hN, inv_g hM]
  by_contra h
  rw [not_le] at h
  have := g_strictMono (Set.mem_Ici.mpr hM) (Set.mem_Ici.mpr hN) h
  linarith

lemma inv_convex : ConvexOn ℝ (Ici 0) thermalEntropyInverse := by
  refine ⟨convex_Ici 0, fun s hs t ht a b ha hb hab => ?_⟩
  obtain ⟨N, hN, rfl⟩ := surj hs
  obtain ⟨M, hM, rfl⟩ := surj ht
  rw [inv_g hN, inv_g hM]
  have hc := g_concave.2 (Set.mem_Ici.mpr hN) (Set.mem_Ici.mpr hM) ha hb hab
  have hmem : a • N + b • M ∈ Ici (0:ℝ) := by
    simp only [smul_eq_mul, mem_Ici]; positivity
  have hmem' : a • g N + b • g M ∈ Ici (0:ℝ) := by
    simp only [smul_eq_mul, mem_Ici]
    have := g_nonneg hN; have := g_nonneg hM; positivity
  have := inv_mono hmem' (Set.mem_Ici.mpr (g_nonneg (Set.mem_Ici.mp hmem))) hc
  rw [inv_g (Set.mem_Ici.mp hmem)] at this
  exact this

theorem props :
    (∀ N : ℝ, 0 ≤ N → 0 ≤ g N) ∧
    MonotoneOn g (Set.Ici 0) ∧ ConcaveOn ℝ (Set.Ici 0) g ∧
    (∀ S : ℝ, 0 ≤ S → 0 ≤ thermalEntropyInverse S) ∧
    MonotoneOn thermalEntropyInverse (Set.Ici 0) ∧
    ConvexOn ℝ (Set.Ici 0) thermalEntropyInverse ∧
    (∀ N : ℝ, 0 ≤ N → thermalEntropyInverse (g N) = N) ∧
    (∀ S : ℝ, 0 ≤ S → g (thermalEntropyInverse S) = S) :=
  ⟨fun _ h => g_nonneg h, g_mono, g_concave, fun _ h => inv_nonneg h, inv_mono, inv_convex,
    fun _ h => inv_g h, fun _ h => g_inv h⟩

lemma diff_mono (c : ℝ) (hc : 0 ≤ c) (hc_one : c < 1) :
    MonotoneOn (fun x : ℝ => g x - g (c * x)) (Set.Ici 0) := by
  rcases hc.eq_or_lt with rfl | hc0
  · simp only [zero_mul, g_zero, sub_zero]; exact g_mono
  have hd : ∀ x, 0 < x → HasDerivAt (fun x : ℝ => g x - g (c * x))
      ((log (x + 1) - log x) - (log (c * x + 1) - log (c * x)) * c) x := by
    intro x hx
    have h2 := (g_hasDeriv (mul_pos hc0 hx)).comp x ((hasDerivAt_id x).const_mul c)
    simp only [mul_one] at h2
    exact (g_hasDeriv hx).sub h2
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
    ((g_cont.sub (g_cont.comp (continuous_const.mul continuous_id))).continuousOn) ?_ ?_
  · rw [interior_Ici]; intro x hx; exact (hd x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]; intro x hx
    simp only [mem_Ioi] at hx
    rw [(hd x hx).deriv]
    have hcx : 0 < c * x := mul_pos hc0 hx
    -- c log(1 + 1/(cx)) ≤ log(1 + 1/x) by concavity of log
    have key := (strictConcaveOn_log_Ioi.concaveOn).2 (show (1 + 1 / (c * x)) ∈ Ioi (0:ℝ) by
        simp only [mem_Ioi]; positivity) (show (1:ℝ) ∈ Ioi 0 by norm_num)
      hc (by linarith : (0:ℝ) ≤ 1 - c) (by ring)
    simp only [smul_eq_mul, log_one, mul_zero, add_zero] at key
    have e1 : c * (1 + 1 / (c * x)) + (1 - c) * 1 = (x + 1) / x := by
      field_simp; ring
    have e2 : log (1 + 1 / (c * x)) = log (c * x + 1) - log (c * x) := by
      rw [← log_div (by positivity) hcx.ne']; congr 1; field_simp
    rw [e1, log_div (by positivity) hx.ne', e2] at key
    nlinarith

end X4P06

-- ===== P06Sol1 =====

noncomputable section

open MeasureTheory Filter

open scoped ENNReal BigOperators Topology

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution (c : ℝ) (hc : 0 ≤ c) (hc_one : c < 1) :
    MonotoneOn (fun x : ℝ => g x - g (c * x)) (Set.Ici 0) :=
  X4P06.diff_mono c hc hc_one

end

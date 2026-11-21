-- Prove2me | solution 1 for Titchmarsh.inv_riemannZeta_le_rpow_of_riemannHypothesis
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:24:37.55355+00:00
-- url     : https://prove2.me/submissions/3733bd8d-1a33-4f49-b9ac-84e1869b965e

import Theorems.Thm_OAI_SevenEighths_LogarithmicControl_logarithmic_control
import Theorems.Thm_OAI_SevenEighths_LogarithmicControl_exists_holomorphic_log_normalized
import Theorems.Thm_OAI_SevenEighths_LogarithmicControl_borel_caratheodory_closedBall
import Theorems.Thm_Zeta23_RvM_norm_riemannZeta_le_of_re_pos
import Theorems.Thm_Zeta23_RvM_norm_riemannZeta_sub_one_le

set_option autoImplicit false

open Complex Metric Set

namespace RHInvZeta

/-- The value `∑ n^{-3/2}`, a uniform bound for `‖ζ‖` on `Re ≥ 3/2`. -/
noncomputable def K₀ : ℝ := ∑' n : ℕ, ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹

lemma summable_K₀ : Summable (fun n : ℕ => ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
  Real.summable_nat_rpow_inv.mpr (by norm_num)

lemma norm_term_le (z : ℂ) (hz : 3 / 2 ≤ z.re) (n : ℕ) :
    ‖1 / (n : ℂ) ^ z‖ ≤ ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hz0 : z ≠ 0 := by
      intro h; rw [h] at hz; simp at hz; linarith
    simp [Complex.zero_cpow hz0]
  · rw [norm_div, norm_one, norm_natCast_cpow_of_pos hn, one_div]
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact inv_anti₀ (by positivity) (Real.rpow_le_rpow_of_exponent_le h1 hz)

lemma norm_zeta_le_K₀ {z : ℂ} (hz : 3 / 2 ≤ z.re) : ‖riemannZeta z‖ ≤ K₀ := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by linarith)]
  have hsum : Summable (fun n : ℕ => ‖1 / (n : ℂ) ^ z‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (norm_term_le z hz) summable_K₀
  exact (norm_tsum_le_tsum_norm hsum).trans (hsum.tsum_le_tsum (norm_term_le z hz) summable_K₀)

lemma pi_sq_div_six_lt : Real.pi ^ 2 / 6 < 5 / 3 := by
  have h1 := Real.pi_lt_d2
  have h0 := Real.pi_pos
  nlinarith

lemma norm_zeta_ge {s : ℂ} (hs : 2 ≤ s.re) : 2 - Real.pi ^ 2 / 6 ≤ ‖riemannZeta s‖ := by
  have h := Zeta23.RvM.norm_riemannZeta_sub_one_le hs
  have h2 : ‖(1 : ℂ)‖ ≤ ‖riemannZeta s‖ + ‖riemannZeta s - 1‖ := by
    have := norm_sub_le (riemannZeta s) (riemannZeta s - 1)
    simpa using this
  simp at h2
  linarith

lemma norm_zeta_le_two {s : ℂ} (hs : 2 ≤ s.re) : ‖riemannZeta s‖ ≤ 2 := by
  have h := Zeta23.RvM.norm_riemannZeta_sub_one_le hs
  have h2 : ‖riemannZeta s‖ ≤ ‖riemannZeta s - 1‖ + ‖(1 : ℂ)‖ := by
    have := norm_add_le (riemannZeta s - 1) 1
    simpa using this
  have := pi_sq_div_six_lt
  simp at h2
  linarith

lemma lower_pos : 0 < 2 - Real.pi ^ 2 / 6 := by
  have := pi_sq_div_six_lt; linarith

/-- Under RH, no zeros in `Re s > 1/2` other than possibly `s = 1`. -/
lemma zeta_ne_zero_of_RH (hRH : RiemannHypothesis) {s : ℂ}
    (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro h0
  have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [this] at hs
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have := hRH s h0 htriv hs1
  linarith

/-- `|log x| ≤ x + 1/x` for `x > 0`. -/
lemma abs_log_le (x : ℝ) (hx : 0 < x) : |Real.log x| ≤ x + x⁻¹ := by
  rw [abs_le]
  constructor
  · have := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
    rw [Real.log_inv] at this
    have : 0 < x := hx
    linarith
  · have := Real.log_le_sub_one_of_pos hx
    have : 0 < x⁻¹ := inv_pos.mpr hx
    linarith

lemma norm_log_le (w : ℂ) (hw : w ≠ 0) : ‖Complex.log w‖ ≤ ‖w‖ + ‖w‖⁻¹ + Real.pi := by
  have h1 : ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| := Complex.norm_le_abs_re_add_abs_im _
  rw [Complex.log_re, Complex.log_im] at h1
  have h2 := abs_log_le ‖w‖ (norm_pos_iff.mpr hw)
  have h3 : |w.arg| ≤ Real.pi := Complex.abs_arg_le_pi w
  linarith

/-! ### A holomorphic logarithm of `ζ` near `Re s = 2`, bounded uniformly in the height -/

noncomputable def Mre : ℝ := |Real.log K₀| + 1
noncomputable def Ac : ℝ := 2 + (2 - Real.pi ^ 2 / 6)⁻¹ + Real.pi
noncomputable def A₁ : ℝ :=
  max (2 * Mre * (49 / 100) / (1 / 2 - 49 / 100) + Ac * (1 / 2 + 49 / 100) / (1 / 2 - 49 / 100)) 1

lemma Mre_pos : 0 < Mre := by unfold Mre; positivity

lemma Ac_nonneg : 0 ≤ Ac := by
  unfold Ac; have := lower_pos; have := Real.pi_pos; positivity

lemma re_sub_le {z c : ℂ} {r : ℝ} (hz : z ∈ ball c r) : |z.re - c.re| < r := by
  rw [mem_ball, dist_eq_norm] at hz
  have := Complex.abs_re_le_norm (z - c)
  rw [sub_re] at this
  linarith

lemma im_sub_le {z c : ℂ} {r : ℝ} (hz : z ∈ ball c r) : |z.im - c.im| < r := by
  rw [mem_ball, dist_eq_norm] at hz
  have := Complex.abs_im_le_norm (z - c)
  rw [sub_im] at this
  linarith

lemma exists_log_small (c : ℂ) (hc : c.re = 2) :
    ∃ E : ℂ → ℂ, DifferentiableOn ℂ E (ball c (1 / 2)) ∧
      EqOn (Complex.exp ∘ E) riemannZeta (ball c (1 / 2)) ∧
      ∀ z ∈ closedBall c (49 / 100), ‖E z‖ ≤ A₁ := by
  have hre : ∀ z ∈ ball c (1 / 2), 3 / 2 < z.re := by
    intro z hz
    have := re_sub_le hz
    rw [hc] at this
    linarith [(abs_lt.mp this).1]
  have hne1 : ∀ z ∈ ball c (1 / 2), z ≠ 1 := by
    intro z hz h
    have := hre z hz
    rw [h] at this
    norm_num at this
  have hdiff : DifferentiableOn ℂ riemannZeta (ball c (1 / 2)) := fun z hz =>
    (differentiableAt_riemannZeta (hne1 z hz)).differentiableWithinAt
  have hnz : ∀ z ∈ ball c (1 / 2), riemannZeta z ≠ 0 := fun z hz =>
    riemannZeta_ne_zero_of_one_lt_re (by linarith [hre z hz])
  have hc0 : riemannZeta c ≠ 0 := hnz c (mem_ball_self (by norm_num))
  obtain ⟨E, hEd, hEeq, hEc⟩ :=
    OAI.SevenEighths.LogarithmicControl.exists_holomorphic_log_normalized (by norm_num) hdiff hnz
      (Complex.exp_log hc0)
  refine ⟨E, hEd, hEeq, ?_⟩
  intro z hz
  have hRe : ∀ w ∈ ball c (1 / 2), (E w).re ≤ Mre := by
    intro w hw
    have h1 : Complex.exp (E w) = riemannZeta w := hEeq hw
    have h2 : Real.exp (E w).re = ‖riemannZeta w‖ := by rw [← Complex.norm_exp, h1]
    have h3 : (E w).re = Real.log ‖riemannZeta w‖ := by rw [← h2, Real.log_exp]
    rw [h3]
    have hpos : 0 < ‖riemannZeta w‖ := norm_pos_iff.mpr (hnz w hw)
    have hle := norm_zeta_le_K₀ (le_of_lt (hre w hw))
    have h4 : Real.log ‖riemannZeta w‖ ≤ Real.log K₀ := Real.log_le_log hpos hle
    unfold Mre
    linarith [le_abs_self (Real.log K₀)]
  have hcA : ‖E c‖ ≤ Ac := by
    rw [hEc]
    refine (norm_log_le _ hc0).trans ?_
    have hge := norm_zeta_ge (s := c) (by rw [hc])
    have hle := norm_zeta_le_two (s := c) (by rw [hc])
    have hinv : ‖riemannZeta c‖⁻¹ ≤ (2 - Real.pi ^ 2 / 6)⁻¹ := inv_anti₀ lower_pos hge
    unfold Ac
    linarith
  have hbc := OAI.SevenEighths.LogarithmicControl.borel_caratheodory_closedBall
    (g := E) (c := c) (r := 49 / 100) (R := 1 / 2) (M := Mre) (A := Ac)
    (by norm_num) (by norm_num) Mre_pos Ac_nonneg hEd hRe hcA hz
  exact hbc.trans (le_max_left _ _)

/-! ### The main estimate for `|Im s| ≥ 2`, `1/2 + δ ≤ Re s ≤ 2` -/

lemma main_bound (hRH : RiemannHypothesis) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ s : ℂ, 1 / 2 + δ ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| →
      ‖(riemannZeta s)⁻¹‖ ≤ D * (|s.im| + 4) ^ ε := by
  set e : ℝ := min (δ / 6) (1 / 2000) with he_def
  have he : 0 < e := lt_min (by linarith) (by norm_num)
  have he' : e < 1 / 1000 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have he6 : 6 * e ≤ δ := by have := min_le_left (δ / 6) (1 / 2000); linarith
  obtain ⟨D, hD, hDprop⟩ := OAI.SevenEighths.LogarithmicControl.logarithmic_control
    (e := e) (A := A₁) (M := 2) (ε := ε) he he' (le_max_right _ _) (by norm_num) hε
  refine ⟨D, hD, ?_⟩
  intro s hs1 hs2 ht
  set c : ℂ := 2 + (s.im : ℂ) * I with hc_def
  have hcre : c.re = 2 := by simp [c]
  have hcim : c.im = s.im := by simp [c]
  obtain ⟨E, hEd, hEeq, hEb⟩ := exists_log_small c hcre
  -- geometry of the big disc
  have hgeo : ∀ z ∈ ball c (2 - 1 / 2 - 2 * e),
      1 / 2 + 2 * e < z.re ∧ z.re < 4 ∧ 1 / 2 < |z.im| ∧ |z.im| < |s.im| + 3 / 2 := by
    intro z hz
    have h1 := abs_lt.mp (re_sub_le hz)
    have h2 := abs_lt.mp (im_sub_le hz)
    rw [hcre] at h1
    rw [hcim] at h2
    refine ⟨by linarith, by linarith, ?_, ?_⟩
    · rcases le_or_gt 0 s.im with h | h
      · rw [abs_of_nonneg h] at ht
        rw [lt_abs]; left; linarith
      · rw [abs_of_neg h] at ht
        rw [lt_abs]; right; linarith
    · rcases le_or_gt 0 s.im with h | h
      · rw [abs_of_nonneg h]; rw [abs_lt]; constructor <;> linarith
      · rw [abs_of_neg h]; rw [abs_lt]; constructor <;> linarith
  have hne1 : ∀ z ∈ ball c (2 - 1 / 2 - 2 * e), z ≠ 1 := by
    intro z hz h
    have := (hgeo z hz).2.2.1
    rw [h] at this
    norm_num at this
  have hL : DifferentiableOn ℂ riemannZeta (ball c (2 - 1 / 2 - 2 * e)) := fun z hz =>
    (differentiableAt_riemannZeta (hne1 z hz)).differentiableWithinAt
  have h0 : ∀ z ∈ ball c (2 - 1 / 2 - 2 * e), riemannZeta z ≠ 0 := fun z hz =>
    zeta_ne_zero_of_RH hRH (by linarith [(hgeo z hz).1]) (hne1 z hz)
  have hsub : ball c (2 - 1 / 2 - 3 * e) ⊆ ball c (2 - 1 / 2 - 2 * e) :=
    ball_subset_ball (by linarith)
  have hpoly : ∀ z ∈ ball c (2 - 1 / 2 - 3 * e), ‖riemannZeta z‖ ≤ (|s.im| + 4) ^ (2 : ℝ) := by
    intro z hz
    obtain ⟨hzre, hzre4, hzim, hzim2⟩ := hgeo z (hsub hz)
    have hzre0 : 0 < z.re := by linarith
    have hb := Zeta23.RvM.norm_riemannZeta_le_of_re_pos hzre0 (hne1 z (hsub hz))
    have h1 : 1 / 2 < ‖1 - z‖ := by
      have := Complex.abs_im_le_norm (1 - z)
      simp only [sub_im, one_im, zero_sub, abs_neg] at this
      linarith
    have h2 : 1 / ‖1 - z‖ ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have h3 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hzre0] at h3
    have h4 : ‖z‖ / z.re ≤ 2 * ‖z‖ := by
      rw [div_le_iff₀ hzre0]; nlinarith [norm_nonneg z]
    rw [Real.rpow_two]
    have habs : 0 ≤ |s.im| := abs_nonneg _
    nlinarith
  have hC : Real.exp 1 ≤ |s.im| + 4 := by
    have := Real.exp_one_lt_d9
    linarith
  have hs_mem : s ∈ closedBall c (2 - 1 / 2 - 6 * e) := by
    rw [mem_closedBall, dist_eq_norm]
    have hsc : s - c = ((s.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [c]
    rw [hsc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have key := (hDprop (1 / 2) (|s.im| + 4) riemannZeta E c (le_refl _) (by norm_num) hC hL h0
    hpoly hEd hEeq hEb).1 s hs_mem
  linarith [norm_nonneg (riemannZeta s)]

end RHInvZeta

open RHInvZeta in
theorem inv_zeta_bound_all (hRH : RiemannHypothesis) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ s : ℂ, 1 / 2 + δ ≤ s.re → 1 ≤ |s.im| →
      ‖(riemannZeta s)⁻¹‖ ≤ C * |s.im| ^ ε := by
  obtain ⟨D, hD, hmain⟩ := main_bound hRH δ ε hδ hε
  set K : Set ℂ := {s | 1 / 2 + δ ≤ s.re} ∩ {s | s.re ≤ 2} ∩ {s | 1 ≤ |s.im|} ∩ {s | |s.im| ≤ 2}
    with hK
  have hKclosed : IsClosed K := by
    refine ((IsClosed.inter (IsClosed.inter ?_ ?_) ?_)).inter ?_
    · exact isClosed_le continuous_const Complex.continuous_re
    · exact isClosed_le Complex.continuous_re continuous_const
    · exact isClosed_le continuous_const (continuous_abs.comp Complex.continuous_im)
    · exact isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const
  have hKbdd : Bornology.IsBounded K := by
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 4)).subset ?_
    rintro s ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    simp only [Set.mem_ofPred_eq] at h1 h2 h3 h4
    rw [mem_closedBall, dist_zero_right]
    have := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos (by linarith)] at this
    linarith
  have hKc : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKclosed hKbdd
  have hcont : ContinuousOn (fun s => (riemannZeta s)⁻¹) K := by
    rintro s ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    simp only [Set.mem_ofPred_eq] at h1 h2 h3 h4
    have hs1 : s ≠ 1 := by
      intro h; rw [h] at h3; norm_num at h3
    have hnz : riemannZeta s ≠ 0 := zeta_ne_zero_of_RH hRH (by linarith) hs1
    exact ((differentiableAt_riemannZeta hs1).continuousAt.inv₀ hnz).continuousWithinAt
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hcont
  have hlow : 0 < (2 - Real.pi ^ 2 / 6)⁻¹ := inv_pos.mpr lower_pos
  set C : ℝ := max (D * 3 ^ ε) (max B (2 - Real.pi ^ 2 / 6)⁻¹) with hC_def
  have hCpos : 0 < C := lt_of_lt_of_le hlow (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨C, ?_⟩
  intro s hs ht
  have hpow1 : 1 ≤ |s.im| ^ ε := Real.one_le_rpow ht hε.le
  have hconst : ∀ X : ℝ, X ≤ C → ‖(riemannZeta s)⁻¹‖ ≤ X → ‖(riemannZeta s)⁻¹‖ ≤ C * |s.im| ^ ε :=
    fun X hX h => by nlinarith
  by_cases hre2 : 2 < s.re
  · refine hconst _ (le_trans (le_max_right _ _) (le_max_right _ _)) ?_
    rw [norm_inv]
    exact inv_anti₀ lower_pos (norm_zeta_ge hre2.le)
  · replace hre2 := not_lt.mp hre2
    by_cases ht2 : 2 ≤ |s.im|
    · have h := hmain s hs hre2 ht2
      have h3 : (|s.im| + 4) ^ ε ≤ 3 ^ ε * |s.im| ^ ε := by
        rw [← Real.mul_rpow (by norm_num) (abs_nonneg _)]
        exact Real.rpow_le_rpow (by positivity) (by linarith) hε.le
      calc ‖(riemannZeta s)⁻¹‖ ≤ D * (|s.im| + 4) ^ ε := h
        _ ≤ D * (3 ^ ε * |s.im| ^ ε) := mul_le_mul_of_nonneg_left h3 hD.le
        _ = (D * 3 ^ ε) * |s.im| ^ ε := by ring
        _ ≤ C * |s.im| ^ ε :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · replace ht2 := not_le.mp ht2
      have hsK : s ∈ K := ⟨⟨⟨hs, hre2⟩, ht⟩, ht2.le⟩
      refine hconst _ (le_trans (le_max_left _ _) (le_max_right _ _)) ?_
      have := hB s hsK
      simpa using this

theorem solution (hRH : RiemannHypothesis) :
    ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ s : ℂ,
      1 / 2 + δ ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
        ‖(riemannZeta s)⁻¹‖ ≤ C * |s.im| ^ ε := by
  intro δ hδ ε hε
  obtain ⟨C, hC⟩ := inv_zeta_bound_all hRH δ ε hδ hε
  exact ⟨C, fun s h1 _ h3 => hC s h1 h3⟩

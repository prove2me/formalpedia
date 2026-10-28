-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P15.remark9
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:23:18.757895+00:00
-- url     : https://prove2.me/submissions/bbddf4e9-3f78-4347-98d1-381157bee94b

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

section X5mod_RM_A
open Real Filter Set Topology

namespace X5RM

noncomputable def g (ℓ x : ℝ) : ℝ := (x + ℓ) ^ 2 * (exp x / (1 + exp x) ^ 2)

lemma g_cont (ℓ : ℝ) : Continuous (g ℓ) := by
  unfold g
  exact ((continuous_id.add continuous_const).pow 2).mul
    (continuous_exp.div ((continuous_const.add continuous_exp).pow 2) fun x => by positivity)

lemma g_zero (ℓ : ℝ) : g ℓ 0 = ℓ ^ 2 / 4 := by
  simp only [g, exp_zero, zero_add]; ring

lemma g_upper (ℓ x : ℝ) (hx : 0 < x) : g ℓ x < ℓ ^ 2 / 4 + 1 := by
  have hs := Real.self_lt_sinh_iff.2 (half_pos hx)
  rw [Real.sinh_eq, Real.exp_neg] at hs
  set s := exp (x / 2) with hsdef
  have hs0 : 0 < s := exp_pos _
  have he : exp x = s ^ 2 := by rw [hsdef, ← Real.exp_nat_mul]; ring_nf
  have h1 : x * s < s ^ 2 - 1 := by
    have h' : x < s - s⁻¹ := by linarith
    have := mul_lt_mul_of_pos_right h' hs0
    rwa [sub_mul, inv_mul_cancel₀ hs0.ne', ← sq] at this
  have h2 : x ^ 2 * s ^ 2 < (s ^ 2 - 1) ^ 2 := by
    have : 0 < x * s := by positivity
    nlinarith
  have hcs : (x + ℓ) ^ 2 ≤ (ℓ ^ 2 + 4) * (1 + x ^ 2 / 4) := by
    nlinarith [sq_nonneg (ℓ * x / 2 - 2)]
  unfold g
  rw [he, mul_div_assoc', div_lt_iff₀ (by positivity)]
  have h3 : (x + ℓ) ^ 2 * s ^ 2 ≤ (ℓ ^ 2 + 4) * (1 + x ^ 2 / 4) * s ^ 2 :=
    mul_le_mul_of_nonneg_right hcs (by positivity)
  have h4 : (ℓ ^ 2 / 4 + 1) * (x ^ 2 * s ^ 2) < (ℓ ^ 2 / 4 + 1) * (s ^ 2 - 1) ^ 2 :=
    mul_lt_mul_of_pos_left h2 (by positivity)
  nlinarith

lemma g_one_lower (ℓ : ℝ) (h0 : 0 ≤ ℓ) (h4 : ℓ ≤ 4) : ℓ ^ 2 / 4 < g ℓ 1 := by
  have e1 := Real.exp_one_gt_d9
  have e2 := Real.exp_one_lt_d9
  have hE : (0.195 : ℝ) < exp 1 / (1 + exp 1) ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  unfold g
  have : (1 + ℓ) ^ 2 * 0.195 ≤ (1 + ℓ) ^ 2 * (exp 1 / (1 + exp 1) ^ 2) :=
    mul_le_mul_of_nonneg_left hE.le (by positivity)
  nlinarith

lemma g_asym (y : ℝ) (hy0 : 0 < y) (hy : y ≤ 1 / 2) :
    1 / y ^ 2 + 1 - 5 * y ^ 2 / 4 ≤ g (2 / y) (2 * y) := by
  set t := exp y with htdef
  have ht0 : 0 < t := exp_pos _
  have hc := Real.cosh_le_exp_half_sq y
  rw [Real.cosh_eq, Real.exp_neg, ← htdef] at hc
  have hq : exp (y ^ 2) ≤ 1 + y ^ 2 + (y ^ 2) ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le (x := y ^ 2) (by rw [abs_of_nonneg (by positivity)]; nlinarith)
    have := (abs_le.1 this).2; linarith
  have hc2 : ((t + t⁻¹) / 2) ^ 2 ≤ 1 + y ^ 2 + y ^ 4 := by
    have h0 : 0 ≤ (t + t⁻¹) / 2 := by positivity
    have := pow_le_pow_left₀ h0 hc 2
    rw [← Real.exp_nat_mul] at this
    have e : ((2 : ℕ) : ℝ) * (y ^ 2 / 2) = y ^ 2 := by push_cast; ring
    rw [e] at this
    nlinarith
  set q := 1 + y ^ 2 + y ^ 4 with hqdef
  have hq0 : 0 < q := by positivity
  have hkey : (1 + t ^ 2) ^ 2 ≤ 4 * q * t ^ 2 := by
    have e : (1 + t ^ 2) = 2 * t * ((t + t⁻¹) / 2) := by field_simp; ring
    rw [e]; nlinarith [sq_nonneg t]
  have he2 : exp (2 * y) = t ^ 2 := by rw [htdef, ← Real.exp_nat_mul]; ring_nf
  unfold g
  rw [he2]
  have hA : 1 / (4 * q) ≤ t ^ 2 / (1 + t ^ 2) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hB : (2 * y + 2 / y) ^ 2 * (1 / (4 * q)) = (1 + y ^ 2) ^ 2 / (y ^ 2 * q) := by
    field_simp; ring
  calc 1 / y ^ 2 + 1 - 5 * y ^ 2 / 4 ≤ (2 * y + 2 / y) ^ 2 * (1 / (4 * q)) := by
        rw [hB, le_div_iff₀ (by positivity)]
        have e : (1 / y ^ 2 + 1 - 5 * y ^ 2 / 4) * (y ^ 2 * q) = (1 + y ^ 2 - 5 * y ^ 4 / 4) * q := by
          field_simp
        rw [e, hqdef]
        nlinarith [pow_pos hy0 4, pow_pos hy0 6, pow_pos hy0 8]
    _ ≤ _ := mul_le_mul_of_nonneg_left hA (sq_nonneg _)

lemma g_witness (ℓ : ℝ) (h0 : 0 ≤ ℓ) : ∃ x1 > 0, ℓ ^ 2 / 4 < g ℓ x1 := by
  rcases le_or_gt ℓ 4 with h4 | h4
  · exact ⟨1, one_pos, g_one_lower ℓ h0 h4⟩
  · have hl : 0 < ℓ := by linarith
    have hy0 : 0 < 2 / ℓ := by positivity
    have hy : 2 / ℓ ≤ 1 / 2 := by rw [div_le_iff₀ hl]; linarith
    have := g_asym (2 / ℓ) hy0 hy
    rw [show 2 / (2 / ℓ) = ℓ by field_simp] at this
    refine ⟨2 * (2 / ℓ), by positivity, lt_of_lt_of_le ?_ this⟩
    have e : 1 / (2 / ℓ) ^ 2 = ℓ ^ 2 / 4 := by field_simp; ring
    rw [e]
    have : 5 * (2 / ℓ) ^ 2 / 4 < 1 := by
      rw [div_pow, show 5 * (2 ^ 2 / ℓ ^ 2) / 4 = 5 / ℓ ^ 2 by ring, div_lt_one (by positivity)]
      nlinarith
    linarith

lemma g_tail (ℓ x : ℝ) : g ℓ x ≤ (x + ℓ) ^ 2 * exp (-x) := by
  unfold g
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  rw [Real.exp_neg, div_le_iff₀ (by positivity)]
  have h := exp_pos x
  rw [← div_eq_inv_mul, le_div_iff₀ h]
  nlinarith

lemma tail_tendsto (ℓ : ℝ) : Tendsto (fun x => (x + ℓ) ^ 2 * exp (-x)) atTop (𝓝 0) := by
  have h2 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
  have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h0 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
  have := (h2.add ((h1.const_mul (2 * ℓ)))).add (h0.const_mul (ℓ ^ 2))
  simp only [mul_zero, add_zero] at this
  refine this.congr fun x => ?_
  ring

theorem g_max (ℓ : ℝ) (h0 : 0 ≤ ℓ) :
    ∃ x0 > 0, (∀ x > 0, g ℓ x ≤ g ℓ x0) ∧ ℓ ^ 2 / 4 < g ℓ x0 := by
  obtain ⟨x1, hx1, hg1⟩ := g_witness ℓ h0
  have hpos : 0 < g ℓ x1 := lt_of_le_of_lt (by positivity) hg1
  obtain ⟨X, hX⟩ := eventually_atTop.1 ((tail_tendsto ℓ).eventually (gt_mem_nhds hpos))
  set X' := max X (x1 + 1)
  obtain ⟨x0, hx0, hmax⟩ := isCompact_Icc.exists_isMaxOn (s := Icc 0 X')
    ⟨0, le_rfl, by positivity⟩ (g_cont ℓ).continuousOn
  have hx1m : x1 ∈ Icc 0 X' := ⟨hx1.le, le_trans (by linarith) (le_max_right _ _)⟩
  have hge : g ℓ x1 ≤ g ℓ x0 := hmax hx1m
  have hne : x0 ≠ 0 := by
    rintro rfl; rw [g_zero] at hge; linarith
  refine ⟨x0, lt_of_le_of_ne hx0.1 hne.symm, fun x hx => ?_, lt_of_lt_of_le hg1 hge⟩
  rcases le_or_gt x X' with h | h
  · exact hmax ⟨hx.le, h⟩
  · have := hX x (le_trans (le_max_left _ _) h.le)
    linarith [g_tail ℓ x]

lemma g_deriv (ℓ x : ℝ) : HasDerivAt (g ℓ)
    ((x + ℓ) * exp x / (1 + exp x) ^ 2 * (2 + (x + ℓ) * (1 - exp x) / (1 + exp x))) x := by
  have hE : HasDerivAt (fun x => exp x / (1 + exp x) ^ 2)
      ((exp x * (1 + exp x) ^ 2 - exp x * (2 * (1 + exp x) * exp x)) / ((1 + exp x) ^ 2) ^ 2) x := by
    have h1 : HasDerivAt (fun x => (1 + exp x) ^ 2) (2 * (1 + exp x) * exp x) x := by
      have := ((hasDerivAt_exp x).const_add 1).fun_pow 2
      simpa [mul_comm, mul_assoc, mul_left_comm] using this
    exact (hasDerivAt_exp x).div h1 (by positivity)
  have hP : HasDerivAt (fun x => (x + ℓ) ^ 2) (2 * (x + ℓ)) x := by
    have := ((hasDerivAt_id x).add_const ℓ).fun_pow 2
    simpa using this
  have := hP.fun_mul hE
  unfold g
  refine this.congr_deriv ?_
  have h0 : 1 + exp x ≠ 0 := by positivity
  field_simp
  ring

theorem g_crit (ℓ x0 : ℝ) (h0 : 0 ≤ ℓ) (hx0 : 0 < x0) (hmax : ∀ x > 0, g ℓ x ≤ g ℓ x0) :
    (x0 + ℓ) * (exp x0 - 1) / (exp x0 + 1) = 2 := by
  have hloc : IsLocalMax (g ℓ) x0 :=
    Filter.eventually_of_mem (Ioi_mem_nhds hx0) fun x hx => hmax x hx
  have h := hloc.hasDerivAt_eq_zero (g_deriv ℓ x0)
  have hA : 0 < (x0 + ℓ) * exp x0 / (1 + exp x0) ^ 2 := by
    have : 0 < x0 + ℓ := by linarith
    positivity
  have h2 := (mul_eq_zero.1 h).resolve_left hA.ne'
  have h3 : 1 + exp x0 ≠ 0 := by positivity
  have h4 : exp x0 + 1 ≠ 0 := by positivity
  field_simp at h2 ⊢
  linarith

end X5RM
end X5mod_RM_A

section X5mod_RM_B
open Real Filter Set Topology

namespace X5RM
open QAlgorithms.Papers.Independent.Support50.P15

variable {d : ℕ}

lemma dpos (hd : 2 ≤ d) : 1 ≤ (d : ℝ) - 1 := by
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

lemma ell_nonneg (hd : 2 ≤ d) : 0 ≤ Real.log ((d : ℝ) - 1) := Real.log_nonneg (dpos hd)

lemma f_eq (hd : 2 ≤ d) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) (1 / 2)) :
    varianceObjective d r = g (Real.log ((d : ℝ) - 1)) (Real.log ((1 - r) / r)) := by
  obtain ⟨h0, h1⟩ := hr
  have he : 0 < (1 - r) / r := div_pos (by linarith) h0
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := lt_of_lt_of_le one_pos (dpos hd)
  unfold varianceObjective g
  rw [Real.exp_log he, Real.log_mul he.ne' hd1.ne',
    show (1 - r) / r / (1 + (1 - r) / r) ^ 2 = r * (1 - r) by field_simp; ring]
  ring

lemma x_r (x : ℝ) (hx : 0 < x) :
    1 / (1 + exp x) ∈ Ioo (0 : ℝ) (1 / 2) ∧ Real.log ((1 - 1 / (1 + exp x)) / (1 / (1 + exp x))) = x := by
  have he : 1 < exp x := Real.one_lt_exp_iff.2 hx
  refine ⟨⟨by positivity, ?_⟩, ?_⟩
  · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  · rw [show (1 - 1 / (1 + exp x)) / (1 / (1 + exp x)) = exp x by field_simp; ring, Real.log_exp]

lemma image_eq (hd : 2 ≤ d) :
    varianceObjective d '' Ioo 0 (1 / 2) = g (Real.log ((d : ℝ) - 1)) '' Ioi 0 := by
  ext v
  constructor
  · rintro ⟨r, hr, rfl⟩
    refine ⟨Real.log ((1 - r) / r), ?_, (f_eq hd hr).symm⟩
    obtain ⟨h0, h1⟩ := hr
    exact Real.log_pos (by rw [one_lt_div h0]; linarith)
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨h1, h2⟩ := x_r x hx
    exact ⟨_, h1, by rw [f_eq hd h1, h2]⟩

lemma maxV (hd : 2 ≤ d) {x0 : ℝ} (hx0 : 0 < x0)
    (hmax : ∀ x > 0, g (Real.log ((d : ℝ) - 1)) x ≤ g (Real.log ((d : ℝ) - 1)) x0) :
    maxVariance d = g (Real.log ((d : ℝ) - 1)) x0 := by
  unfold maxVariance
  rw [image_eq hd]
  exact IsGreatest.csSup_eq ⟨⟨x0, hx0, rfl⟩, by rintro _ ⟨x, hx, rfl⟩; exact hmax x hx⟩

lemma om_spec (hd : 2 ≤ d) :
    optimalMass d ∈ Ioo (0 : ℝ) (1 / 2) ∧ varianceObjective d (optimalMass d) = maxVariance d := by
  obtain ⟨x0, hx0, hmax, -⟩ := g_max _ (ell_nonneg hd)
  have hex : ∃ r : ℝ, r ∈ Ioo (0 : ℝ) (1 / 2) ∧ varianceObjective d r = maxVariance d := by
    obtain ⟨h1, h2⟩ := x_r x0 hx0
    exact ⟨_, h1, by rw [f_eq hd h1, h2, maxV hd hx0 hmax]⟩
  exact Classical.epsilon_spec hex

lemma om_eq (hd : 2 ≤ d) :
    (1 - 2 * optimalMass d) * Real.log ((1 - optimalMass d) / optimalMass d * ((d : ℝ) - 1)) = 2 := by
  obtain ⟨hr, hv⟩ := om_spec hd
  set r := optimalMass d
  set ℓ := Real.log ((d : ℝ) - 1)
  obtain ⟨x0, hx0, hmax, -⟩ := g_max ℓ (ell_nonneg hd)
  obtain ⟨h0, h1⟩ := hr
  have he : 1 < (1 - r) / r := by rw [one_lt_div h0]; linarith
  set x := Real.log ((1 - r) / r)
  have hx : 0 < x := Real.log_pos he
  have hgx : g ℓ x = g ℓ x0 := by rw [← f_eq hd ⟨h0, h1⟩, hv, maxV hd hx0 hmax]
  have hcrit := g_crit ℓ x (ell_nonneg hd) hx fun y hy => hgx ▸ hmax y hy
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := lt_of_lt_of_le one_pos (dpos hd)
  rw [Real.log_mul (by positivity) hd1.ne']
  rw [Real.exp_log (by positivity)] at hcrit
  have e : ((1 - r) / r - 1) / ((1 - r) / r + 1) = 1 - 2 * r := by
    field_simp; ring
  rw [mul_div_assoc, e] at hcrit
  linarith

lemma L_pos (hd : 2 ≤ d) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) (1 / 2)) :
    0 < Real.log ((1 - r) / r * ((d : ℝ) - 1)) := by
  obtain ⟨h0, h1⟩ := hr
  have he : 1 < (1 - r) / r := by rw [one_lt_div h0]; linarith
  exact Real.log_pos (by nlinarith [dpos hd])

lemma L_anti (hd : 2 ≤ d) {r1 r2 : ℝ} (h1 : r1 ∈ Ioo (0 : ℝ) (1 / 2)) (h2 : r2 ∈ Ioo (0 : ℝ) (1 / 2))
    (h : r1 < r2) :
    Real.log ((1 - r2) / r2 * ((d : ℝ) - 1)) < Real.log ((1 - r1) / r1 * ((d : ℝ) - 1)) := by
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := lt_of_lt_of_le one_pos (dpos hd)
  have hlt : (1 - r2) / r2 < (1 - r1) / r1 := by
    rw [div_lt_div_iff₀ h2.1 h1.1]; nlinarith
  have hp : 0 < (1 - r2) / r2 * ((d : ℝ) - 1) := mul_pos (div_pos (by linarith [h2.2]) h2.1) hd1
  exact Real.log_lt_log hp (mul_lt_mul_of_pos_right hlt hd1)

lemma root_unique (hd : 2 ≤ d) {r1 r2 : ℝ} (h1 : r1 ∈ Ioo (0 : ℝ) (1 / 2)) (h2 : r2 ∈ Ioo (0 : ℝ) (1 / 2))
    (e1 : (1 - 2 * r1) * Real.log ((1 - r1) / r1 * ((d : ℝ) - 1)) = 2)
    (e2 : (1 - 2 * r2) * Real.log ((1 - r2) / r2 * ((d : ℝ) - 1)) = 2) : r1 = r2 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := L_anti hd h1 h2 h
    have := L_pos hd h2
    nlinarith [h1.2, h2.2]
  · have := L_anti hd h2 h1 h
    have := L_pos hd h1
    nlinarith [h1.2, h2.2]

end X5RM
end X5mod_RM_B

section X5mod_RM_C
open Real Filter Set Topology

namespace X5RM
open QAlgorithms.Papers.Independent.Support50.P15

variable {d : ℕ}

lemma g_asym_l (ℓ : ℝ) (h4 : 4 ≤ ℓ) : ℓ ^ 2 / 4 + 1 - 5 / ℓ ^ 2 ≤ g ℓ (4 / ℓ) := by
  have hl : 0 < ℓ := by linarith
  have hy0 : 0 < 2 / ℓ := by positivity
  have hy : 2 / ℓ ≤ 1 / 2 := by rw [div_le_iff₀ hl]; linarith
  have := g_asym (2 / ℓ) hy0 hy
  rw [show 2 / (2 / ℓ) = ℓ by field_simp, show 2 * (2 / ℓ) = 4 / ℓ by ring] at this
  refine le_of_eq_of_le ?_ this
  field_simp; ring

lemma ell_ge4 (hd : 100 ≤ d) : 4 ≤ Real.log ((d : ℝ) - 1) := by
  have h99 : (99 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (100 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h1 := Real.exp_one_lt_d9
  have : exp 4 = exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have : exp 1 ^ 4 < 2.7182818286 ^ 4 := pow_lt_pow_left₀ h1 (exp_pos 1).le (by norm_num)
  nlinarith

lemma logd_le (hd : 3 ≤ d) : Real.log d ≤ 2 * Real.log ((d : ℝ) - 1) := by
  have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have := Real.log_pow ((d : ℝ) - 1) 2
  push_cast at this
  rw [← this]
  exact Real.log_le_log (by linarith) (by nlinarith)

theorem part1 (hd : 2 ≤ d) :
    easyVariance d - 1 < maxVariance d ∧ maxVariance d < easyVariance d ∧
      (∃! r : ℝ, r ∈ Set.Ioo 0 (1 / 2) ∧
        (1 - 2 * r) * Real.log ((1 - r) / r * ((d : ℝ) - 1)) = 2) ∧
      (1 - 2 * optimalMass d) * Real.log ((1 - optimalMass d) / optimalMass d * ((d : ℝ) - 1)) = 2 := by
  obtain ⟨x0, hx0, hmax, hlow⟩ := g_max _ (ell_nonneg hd)
  have hM := maxV hd hx0 hmax
  have hup := g_upper (Real.log ((d : ℝ) - 1)) x0 hx0
  refine ⟨?_, ?_, ⟨optimalMass d, ⟨(om_spec hd).1, om_eq hd⟩, fun y hy =>
    root_unique hd hy.1 (om_spec hd).1 hy.2 (om_eq hd)⟩, om_eq hd⟩
  · rw [hM, easyVariance]; linarith
  · rw [hM, easyVariance]; linarith

theorem part2 :
    ∃ c > 0, ∃ d0 : ℕ, 3 ≤ d0 ∧ ∀ d ≥ d0,
      0 ≤ easyVariance d - maxVariance d ∧
      easyVariance d - maxVariance d ≤ c / (Real.log d) ^ 2 ∧
      |optimalMass d - (1 / 2 - 1 / Real.log ((d : ℝ) - 1))| ≤ c / (Real.log d) ^ 2 := by
  refine ⟨20, by norm_num, 100, by norm_num, fun d hd => ?_⟩
  have hd2 : 2 ≤ d := by omega
  set ℓ := Real.log ((d : ℝ) - 1) with hℓ
  have h4 : 4 ≤ ℓ := ell_ge4 hd
  have hl : 0 < ℓ := by linarith
  have hld := logd_le (d := d) (by omega)
  have hd1 : (1 : ℝ) < d := by
    have : (100 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hlogd : 0 < Real.log d := Real.log_pos hd1
  have hsq : (Real.log d) ^ 2 ≤ 4 * ℓ ^ 2 := by nlinarith
  obtain ⟨x0, hx0, hmax, hlow⟩ := g_max ℓ (ell_nonneg hd2)
  have hM := maxV hd2 hx0 hmax
  have hup := g_upper ℓ x0 hx0
  have hE : easyVariance d = ℓ ^ 2 / 4 + 1 := rfl
  refine ⟨by rw [hM, hE]; linarith, ?_, ?_⟩
  · have hg := le_trans (g_asym_l ℓ h4) (hmax (4 / ℓ) (by positivity))
    rw [hM, hE]
    have : 5 / ℓ ^ 2 ≤ 20 / (Real.log d) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  · obtain ⟨hr, -⟩ := om_spec hd2
    have heq := om_eq hd2
    set r := optimalMass d
    obtain ⟨h0, h1⟩ := hr
    have he : 1 < (1 - r) / r := by rw [one_lt_div h0]; linarith
    set x := Real.log ((1 - r) / r)
    have hx : 0 < x := Real.log_pos he
    have hd1' : (0 : ℝ) < (d : ℝ) - 1 := by linarith
    have hL : Real.log ((1 - r) / r * ((d : ℝ) - 1)) = x + ℓ := Real.log_mul (by positivity) hd1'.ne'
    rw [hL] at heq
    set L := x + ℓ
    have hL4 : 4 < L := by simp only [L]; linarith
    have hr4 : 1 / 4 < r := by nlinarith
    have hx1 : x ≤ (1 - r) / r - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have hx2 : (1 - r) / r - 1 = (1 - 2 * r) / r := by field_simp; ring
    have hxL : x * L ≤ 8 := by
      have h' : x * L ≤ (1 - 2 * r) / r * L := mul_le_mul_of_nonneg_right (hx2 ▸ hx1) (by linarith)
      have h'' : (1 - 2 * r) / r * L = 2 / r := by rw [div_mul_eq_mul_div, heq]
      rw [h''] at h'
      have : 2 / r < 8 := by rw [div_lt_iff₀ h0]; linarith
      linarith
    have hrL : r = 1 / 2 - 1 / L := by
      have hL0 : L ≠ 0 := by linarith
      field_simp; linarith
    have hdiff : r - (1 / 2 - 1 / ℓ) = x / (ℓ * L) := by
      rw [hrL]; simp only [L]; field_simp; ring
    rw [hdiff, abs_of_nonneg (by positivity)]
    calc x / (ℓ * L) ≤ 2 / ℓ ^ 2 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have : x * ℓ ≤ x * L := mul_le_mul_of_nonneg_left (by simp only [L]; linarith) hx.le
          nlinarith
      _ ≤ 20 / (Real.log d) ^ 2 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith

theorem rm_main :
    (∀ d : ℕ, 2 ≤ d → easyVariance d - 1 < maxVariance d ∧ maxVariance d < easyVariance d ∧
      (∃! r : ℝ, r ∈ Set.Ioo 0 (1 / 2) ∧
        (1 - 2 * r) * Real.log ((1 - r) / r * ((d : ℝ) - 1)) = 2) ∧
      (1 - 2 * optimalMass d) * Real.log ((1 - optimalMass d) / optimalMass d * ((d : ℝ) - 1)) = 2) ∧
    (∃ c > 0, ∃ d0 : ℕ, 3 ≤ d0 ∧ ∀ d ≥ d0,
      0 ≤ easyVariance d - maxVariance d ∧
      easyVariance d - maxVariance d ≤ c / (Real.log d) ^ 2 ∧
      |optimalMass d - (1 / 2 - 1 / Real.log ((d : ℝ) - 1))| ≤ c / (Real.log d) ^ 2) :=
  ⟨fun _ hd => part1 hd, part2⟩

end X5RM
end X5mod_RM_C

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Support50.P15

theorem solution :
    (∀ d : ℕ, 2 ≤ d → easyVariance d - 1 < maxVariance d ∧ maxVariance d < easyVariance d ∧
      (∃! r : ℝ, r ∈ Set.Ioo 0 (1 / 2) ∧
        (1 - 2 * r) * Real.log ((1 - r) / r * ((d : ℝ) - 1)) = 2) ∧
      (1 - 2 * optimalMass d) * Real.log ((1 - optimalMass d) / optimalMass d * ((d : ℝ) - 1)) = 2) ∧
    (∃ c > 0, ∃ d0 : ℕ, 3 ≤ d0 ∧ ∀ d ≥ d0,
      0 ≤ easyVariance d - maxVariance d ∧
      easyVariance d - maxVariance d ≤ c / (Real.log d) ^ 2 ∧
      |optimalMass d - (1 / 2 - 1 / Real.log ((d : ℝ) - 1))| ≤ c / (Real.log d) ^ 2) :=
  X5RM.rm_main

end

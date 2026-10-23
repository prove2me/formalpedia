-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P07.appendixB_scalar_construction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:58:41.018473+00:00
-- url     : https://prove2.me/submissions/da5fe22a-3b2a-4a42-acf9-8980b4972af0

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
noncomputable section

open Filter Topology

namespace X4P07
open QAlgorithms.Papers.Independent.Frontier18.P07

lemma f_cont : Continuous scalarF := by
  have : scalarF = fun t => t - t * Real.log t := by funext t; simp [scalarF]; ring
  rw [this]; exact continuous_id.sub Real.continuous_mul_log

lemma f_deriv (t : ℝ) (ht : 0 < t) : HasDerivAt scalarF (-Real.log t) t := by
  have h : HasDerivAt (fun x => x * (1 - Real.log x)) (1 * (1 - Real.log t) + t * (0 - t⁻¹)) t :=
    (hasDerivAt_id' t).mul ((hasDerivAt_const t (1:ℝ)).sub (Real.hasDerivAt_log ht.ne'))
  have e : (1 * (1 - Real.log t) + t * (0 - t⁻¹)) = -Real.log t := by field_simp; ring
  rw [e] at h; exact h

lemma f_mono : StrictMonoOn scalarF (Set.Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) f_cont.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [(f_deriv x hx.1).deriv]
  have := Real.log_neg hx.1 hx.2
  linarith

lemma f_zero : scalarF 0 = 0 := by simp [scalarF]
lemma f_one : scalarF 1 = 1 := by simp [scalarF]

lemma inv_spec (y : ℝ) (hy0 : 0 < y) (hy1 : y ≤ 1) :
    0 < scalarInverse y ∧ scalarInverse y ≤ 1 ∧ scalarF (scalarInverse y) = y := by
  obtain ⟨t, ht, hft⟩ : ∃ t ∈ Set.Icc (0:ℝ) 1, scalarF t = y := by
    have := intermediate_value_Icc (zero_le_one' ℝ) f_cont.continuousOn
    rw [f_zero, f_one] at this
    exact this ⟨hy0.le, hy1⟩
  have hl : IsLeast {t : ℝ | t ∈ Set.Icc 0 1 ∧ y ≤ scalarF t} t := by
    refine ⟨⟨ht, hft.ge⟩, ?_⟩
    rintro s ⟨hs, hys⟩
    by_contra h
    push Not at h
    have := f_mono hs ht h
    linarith
  have he : scalarInverse y = t := hl.csInf_eq
  rw [he]
  refine ⟨?_, ht.2, hft⟩
  rcases ht.1.lt_or_eq with h | h
  · exact h
  · subst h; rw [f_zero] at hft; linarith

lemma ln2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
lemma ln2_lt_one : Real.log 2 < 1 := by
  have := Real.log_two_lt_d9; linarith

/-- key data at x ≥ 1 -/
lemma key (x : ℝ) (hx : 1 ≤ x) :
    let t := scalarInverse (Real.log 2 / x)
    0 < t ∧ t ≤ 1 ∧ scalarG x = Real.log 2 / (1 - Real.log t) ∧ scalarG x = x * t := by
  intro t
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < Real.log 2 / x := div_pos ln2_pos hx0
  have hy1 : Real.log 2 / x ≤ 1 := by
    rw [div_le_one hx0]; linarith [ln2_lt_one]
  obtain ⟨h0, h1, hf⟩ := inv_spec _ hy0 hy1
  refine ⟨h0, h1, ?_, rfl⟩
  have hl : Real.log t ≤ 0 := Real.log_nonpos h0.le h1
  have hpos : 0 < 1 - Real.log t := by linarith
  simp only [scalarF] at hf
  show x * t = _
  rw [eq_div_iff hpos.ne']
  field_simp at hf
  linarith [hf]


lemma g_bounds (x : ℝ) (hx : 1 ≤ x) : 0 < scalarG x ∧ scalarG x ≤ Real.log 2 := by
  obtain ⟨h0, h1, hg, -⟩ := key x hx
  have hl : Real.log (scalarInverse (Real.log 2 / x)) ≤ 0 := Real.log_nonpos h0.le h1
  rw [hg]
  refine ⟨div_pos ln2_pos (by linarith), ?_⟩
  rw [div_le_iff₀ (by linarith)]
  nlinarith [ln2_pos]

lemma g_anti : StrictAntiOn scalarG (Set.Ici 1) := by
  intro a ha b hb hab
  obtain ⟨a0, a1, ga, -⟩ := key a ha
  obtain ⟨b0, b1, gb, -⟩ := key b hb
  have ha' : (1:ℝ) ≤ a := ha
  have hb' : (1:ℝ) ≤ b := hb
  set ta := scalarInverse (Real.log 2 / a)
  set tb := scalarInverse (Real.log 2 / b)
  have hya : 0 < Real.log 2 / a := div_pos ln2_pos (by linarith)
  have hyb : 0 < Real.log 2 / b := div_pos ln2_pos (by linarith)
  have fa := (inv_spec _ hya (by rw [div_le_one (by linarith)]; linarith [ln2_lt_one])).2.2
  have fb := (inv_spec _ hyb (by rw [div_le_one (by linarith)]; linarith [ln2_lt_one])).2.2
  have hy : Real.log 2 / b < Real.log 2 / a := div_lt_div_of_pos_left ln2_pos (by linarith) hab
  have ht : tb < ta := by
    by_contra h
    push Not at h
    have := f_mono.monotoneOn ⟨a0.le, a1⟩ ⟨b0.le, b1⟩ h
    rw [fa, fb] at this
    linarith
  have hl : Real.log tb < Real.log ta := Real.log_lt_log b0 ht
  have hla : Real.log ta ≤ 0 := Real.log_nonpos a0.le a1
  rw [ga, gb]
  apply div_lt_div_of_pos_left ln2_pos (by linarith) (by linarith)

def phi (s : ℝ) : ℝ := -(1 - s) * Real.log (1 - s) - s

lemma H_eq (x : ℝ) (hx : 1 ≤ x) : scalarH x = 1 + phi (scalarG x) / Real.log 2 := by
  obtain ⟨h0, h1, hg, hgx⟩ := key x hx
  obtain ⟨g0, -⟩ := g_bounds x hx
  set t := scalarInverse (Real.log 2 / x)
  set g := scalarG x
  have hl : Real.log t ≤ 0 := Real.log_nonpos h0.le h1
  have hlog : Real.log x = Real.log g - Real.log t := by
    rw [← Real.log_div g0.ne' h0.ne', hgx, mul_div_assoc, div_self h0.ne', mul_one]
  have hgt : g * Real.log t = g - Real.log 2 := by
    have : 0 < 1 - Real.log t := by linarith
    rw [hg]; field_simp; ring
  unfold scalarH binaryEntropyBits phi
  rw [hlog]
  have := ln2_pos
  field_simp
  linear_combination (-1 : ℝ) * hgt

lemma phi_cont : Continuous phi := by
  unfold phi
  have h1 : Continuous fun s : ℝ => (1 - s) * Real.log (1 - s) :=
    Real.continuous_mul_log.comp (continuous_const.sub continuous_id)
  have : (fun s : ℝ => -(1 - s) * Real.log (1 - s) - s) = fun s => -((1 - s) * Real.log (1 - s)) - s := by
    funext s; ring
  rw [this]; exact (h1.neg).sub continuous_id

lemma phi_anti : StrictAntiOn phi (Set.Icc 0 (Real.log 2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 _) phi_cont.continuousOn
  intro s hs
  rw [interior_Icc] at hs
  have h1s : 0 < 1 - s := by linarith [hs.2, ln2_lt_one]
  have hd : HasDerivAt phi (Real.log (1 - s)) s := by
    have hL : HasDerivAt (fun s : ℝ => Real.log (1 - s)) ((1 - s)⁻¹ * (0 - 1)) s :=
      (Real.hasDerivAt_log h1s.ne').comp s ((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id' s))
    have hA : HasDerivAt (fun s : ℝ => -(1 - s)) (-(0 - 1)) s :=
      ((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id' s)).neg
    have := (hA.mul hL).sub (hasDerivAt_id' s)
    have e : -(0 - 1) * Real.log (1 - s) + -(1 - s) * ((1 - s)⁻¹ * (0 - 1)) - 1 = Real.log (1 - s) := by
      field_simp; ring
    rw [e] at this; exact this
  rw [hd.deriv]
  exact Real.log_neg h1s (by linarith [hs.1])

lemma phi_zero : phi 0 = 0 := by simp [phi]

lemma g_tendsto : Tendsto scalarG atTop (𝓝 0) := by
  have hup : ∀ x, 1 ≤ x → scalarG x ≤ Real.log 2 / (1 + Real.log x) := by
    intro x hx
    obtain ⟨h0, h1, hg, hgx⟩ := key x hx
    obtain ⟨g0, gl⟩ := g_bounds x hx
    set t := scalarInverse (Real.log 2 / x)
    set g := scalarG x
    have hlog : Real.log x = Real.log g - Real.log t := by
      rw [← Real.log_div g0.ne' h0.ne', hgx, mul_div_assoc, div_self h0.ne', mul_one]
    have hgt : g * Real.log t = g - Real.log 2 := by
      rw [hg]
      have : 0 < 1 - Real.log t := by linarith [Real.log_nonpos h0.le h1]
      field_simp; ring
    have hlg : Real.log g ≤ 0 := Real.log_nonpos g0.le (gl.trans ln2_lt_one.le)
    have hx0 : 0 ≤ Real.log x := Real.log_nonneg hx
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  have hlim : Tendsto (fun x => Real.log 2 / (1 + Real.log x)) atTop (𝓝 0) := by
    apply Tendsto.div_atTop tendsto_const_nhds
    exact tendsto_atTop_add_const_left _ _ Real.tendsto_log_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards [eventually_ge_atTop 1] with x hx using (g_bounds x hx).1.le
  · filter_upwards [eventually_ge_atTop 1] with x hx using hup x hx

end X4P07

open QAlgorithms.Papers.Independent.Frontier18.P07 X4P07 in
theorem solution :
    (∀ x ∈ Set.Ici (1 : ℝ), scalarG x ∈ Set.Icc (0 : ℝ) 1) ∧
    Tendsto scalarG atTop (𝓝 0) ∧
    StrictMonoOn scalarH (Set.Ici (1 : ℝ)) ∧
    (∀ x ∈ Set.Ici (1 : ℝ), scalarH x < 1) ∧
    Tendsto scalarH atTop (𝓝 1) := by
  have l2 := ln2_pos
  have mem : ∀ x : ℝ, 1 ≤ x → scalarG x ∈ Set.Icc 0 (Real.log 2) := fun x hx =>
    ⟨(g_bounds x hx).1.le, (g_bounds x hx).2⟩
  refine ⟨fun x hx => ⟨(g_bounds x hx).1.le, (g_bounds x hx).2.trans ln2_lt_one.le⟩,
    g_tendsto, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    rw [H_eq a ha, H_eq b hb]
    have := phi_anti (mem b hb) (mem a ha) (g_anti ha hb hab)
    have := div_lt_div_of_pos_right this l2
    linarith
  · intro x hx
    rw [H_eq x hx]
    have := phi_anti ⟨le_refl 0, l2.le⟩ (mem x hx) (g_bounds x hx).1
    rw [phi_zero] at this
    have : phi (scalarG x) / Real.log 2 < 0 := div_neg_of_neg_of_pos this l2
    linarith
  · have h : Tendsto (fun x => 1 + phi (scalarG x) / Real.log 2) atTop (𝓝 (1 + phi 0 / Real.log 2)) :=
      tendsto_const_nhds.add ((phi_cont.tendsto 0).comp g_tendsto |>.div_const _)
    rw [phi_zero, zero_div, add_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with x hx using (H_eq x hx).symm

-- Prove2me | solution 1 for PGDMap20261031.power_threshold
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-31T16:40:17.80468+00:00
-- url     : https://prove2.me/submissions/6a6fe500-6c75-482b-8c77-13b843a5db30

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Definitions.Def_PGDMap20261031_Entropy

open PGDMap20261031 Set Filter
open scoped Topology
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

private lemma skew_deriv (c t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
    HasDerivAt (skew c) (c * (1 - skew c t ^ 2) / (1 - t ^ 2)) t := by
  have hplus : 0 < 1 + t := by linarith [ht.1]
  have hminus : 0 < 1 - t := by linarith [ht.2]
  have hp := ((hasDerivAt_id t).const_add 1).rpow_const
    (Or.inl (ne_of_gt hplus) : 1 + t ≠ 0 ∨ 1 ≤ -c)
  have hm := ((hasDerivAt_id t).const_sub 1).rpow_const
    (Or.inl (ne_of_gt hminus) : 1 - t ≠ 0 ∨ 1 ≤ -c)
  have hsum : Real.rpow (1 - t) (-c) + Real.rpow (1 + t) (-c) ≠ 0 :=
    ne_of_gt (add_pos (Real.rpow_pos_of_pos hminus _) (Real.rpow_pos_of_pos hplus _))
  have hden : 1 - t ^ 2 ≠ 0 := ne_of_gt (by nlinarith [ht.1, ht.2])
  convert (hm.sub hp).div (hm.add hp) hsum using 1 <;> try rfl
  unfold skew
  simp only [id_eq, Pi.sub_apply, Pi.add_apply, Real.rpow_eq_pow] at hsum ⊢
  rw [Real.rpow_sub_one (ne_of_gt hplus), Real.rpow_sub_one (ne_of_gt hminus)]
  field_simp [hsum, hden, ne_of_gt hplus, ne_of_gt hminus]
  <;> ring

private lemma skew_one (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : skew 1 t = t := by
  have hm : 1 - t ≠ 0 := ne_of_gt (by linarith [ht.2])
  have hp : 1 + t ≠ 0 := ne_of_gt (by linarith [ht.1])
  have hsum : (1 - t)⁻¹ + (1 + t)⁻¹ ≠ 0 := ne_of_gt
    (add_pos (inv_pos.mpr (by linarith [ht.2])) (inv_pos.mpr (by linarith [ht.1])))
  unfold skew
  simp only [Real.rpow_eq_pow, Real.rpow_neg_one]
  field_simp [hm, hp, hsum]
  <;> ring

private lemma skew_zero (c : ℝ) : skew c 0 = 0 := by simp [skew]

private lemma skew_basic (c t : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (ht : t ∈ Ico (0 : ℝ) 1) : 0 ≤ skew c t ∧ skew c t ≤ t := by
  obtain ⟨h0, h1⟩ := skew_nonneg_mono c 1 t hc0 hc1 ht
  rw [skew_one t ht] at h1
  exact ⟨h0, h1⟩

private lemma skew_lower (c t : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (ht : t ∈ Ico (0 : ℝ) 1) : c * t ≤ skew c t := by
  have hdiff (s : ℝ) (hs : s ∈ Ico (0 : ℝ) 1) :
      HasDerivAt (fun s => skew c s - c * s)
        (c * (1 - skew c s ^ 2) / (1 - s ^ 2) - c) s := by
    convert (skew_deriv c s hs).sub ((hasDerivAt_id s).const_mul c) using 1
      <;> first | rfl | simp
  have hmono : MonotoneOn (fun s => skew c s - c * s) (Ico (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
    · intro s hs
      exact (hdiff s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ico] at hs
      exact (hdiff s ⟨hs.1.le, hs.2⟩).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ico] at hs
      have hs' : s ∈ Ico (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
      rw [(hdiff s hs').deriv]
      have hd : 0 < 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
      have hb := skew_basic c s hc0 hc1 hs'
      have hsq : skew c s ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hb.1 hb.2 2
      have hnum : c * (1 - s ^ 2) ≤ c * (1 - skew c s ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hc0
      have hdiv : c ≤ c * (1 - skew c s ^ 2) / (1 - s ^ 2) :=
        (le_div_iff₀ hd).2 hnum
      simpa only [mul_one] using sub_nonneg.mpr hdiv
  have hz : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have := hmono hz ht ht.1
  simp only [skew_zero, mul_zero, sub_zero] at this
  nlinarith

private lemma skew_complement (c t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
    skew c t + skew (1 - c) t = t * (1 + skew c t * skew (1 - c) t) := by
  have hm : 0 < 1 - t := by linarith [ht.2]
  have hp : 0 < 1 + t := by linarith [ht.1]
  have hmul (v : ℝ) (hv : 0 < v) :
      Real.rpow v (-c) * Real.rpow v (-(1 - c)) = v⁻¹ := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hv]
    rw [show -c + -(1 - c) = (-1 : ℝ) by ring, Real.rpow_neg_one]
  have hsum (d : ℝ) : Real.rpow (1 - t) (-d) + Real.rpow (1 + t) (-d) ≠ 0 :=
    ne_of_gt (add_pos (Real.rpow_pos_of_pos hm _) (Real.rpow_pos_of_pos hp _))
  have hM := hmul (1 - t) hm
  have hP := hmul (1 + t) hp
  have hM' : Real.rpow (1 - t) (-c) * Real.rpow (1 - t) (-(1 - c)) * (1 - t) = 1 := by
    rw [hM, inv_mul_cancel₀ (ne_of_gt hm)]
  have hP' : Real.rpow (1 + t) (-c) * Real.rpow (1 + t) (-(1 - c)) * (1 + t) = 1 := by
    rw [hP, inv_mul_cancel₀ (ne_of_gt hp)]
  unfold skew
  simp only [Real.rpow_eq_pow] at hsum hM' hP' ⊢
  field_simp [hsum c, hsum (1 - c)]
  nlinarith only [hM', hP']

private lemma skew_upper (c t : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (ht : t ∈ Ico (0 : ℝ) 1) :
    skew c t ≤ c * t / (1 - (1 - c) * t ^ 2) := by
  have hb := skew_basic c t hc0 hc1 ht
  have hd : 0 < 1 - (1 - c) * t ^ 2 := by
    nlinarith [sq_nonneg t, hc0, hc1, ht.1, ht.2]
  have hl := skew_lower (1 - c) t (by linarith) (by linarith) ht
  have heq := skew_complement c t ht
  have hts : t * skew c t ≤ 1 := by nlinarith [ht.1, ht.2, hb.1, hb.2]
  have hprod := mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hts)
  apply (le_div_iff₀ hd).2
  nlinarith only [heq, hprod]

private def R (c t : ℝ) : ℝ := c * (t + skew c t) /
  (t * (2 * (1 - t ^ 2) + c * t * (t + skew c t)))

private def H (c t s : ℝ) : ℝ :=
  -c * t ^ 3 - 2 * c * t ^ 2 * s - 2 * c * t * s ^ 2 + c * t +
    2 * t ^ 3 + 3 * t ^ 2 * s - s

private lemma R_den_pos (c t : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < t * (2 * (1 - t ^ 2) + c * t * (t + skew c t)) := by
  have hs := (skew_basic c t hc0.le hc1.le ⟨ht.1.le, ht.2⟩).1
  have hsq : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  exact mul_pos ht.1 (add_pos (mul_pos (by norm_num) hsq)
    (mul_pos (mul_pos hc0 ht.1) (by linarith [ht.1])))

private lemma R_deriv (c t : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) : HasDerivAt (R c)
      (2 * c * H c t (skew c t) /
        (t * (2 * (1 - t ^ 2) + c * t * (t + skew c t))) ^ 2) t := by
  have hs := skew_deriv c t ⟨ht.1.le, ht.2⟩
  have hq := (hasDerivAt_id t).pow 2
  have hden := ne_of_gt (R_den_pos c t hc0 hc1 ht)
  have hsq : 1 - t ^ 2 ≠ 0 := ne_of_gt (by nlinarith [ht.1, ht.2])
  have hsum := (hasDerivAt_id t).add hs
  have hd := (hasDerivAt_id t).mul
    (((hq.const_sub 1).const_mul 2).add
      (((hasDerivAt_id t).const_mul c).mul hsum))
  convert (hsum.const_mul c).div hd hden using 1 <;> try rfl
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id_eq,
    Nat.cast_ofNat, show 2 - 1 = (1 : ℕ) by omega, pow_one, mul_one]
  unfold H
  field_simp [hden, hsq]
  <;> ring

private lemma H_positive (c t : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) : 0 < H c t (skew c t) := by
  let D := 1 - (1 - c) * t ^ 2
  let U := c * t / D
  let l := c * t
  have htp : 0 < t := ht.1
  have hccomp : 0 < 1 - c := by linarith
  have ht2 : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have ht4 : 0 < 1 - t ^ 4 := by nlinarith [sq_nonneg (1 - t ^ 2)]
  have hD : 0 < D := by dsimp [D]; nlinarith [mul_nonneg hc0.le (sq_nonneg t)]
  have hDl : D < 1 := by dsimp [D]; nlinarith [sq_pos_of_pos ht.1]
  have hlU : l < U := by
    dsimp [U, l]
    apply (lt_div_iff₀ hD).2
    simpa only [mul_one] using mul_lt_mul_of_pos_left hDl (mul_pos hc0 ht.1)
  have hlow : 0 < H c t l := by
    have heq : H c t l = 2 * t ^ 3 * (1 - c) * (c + 1) ^ 2 := by dsimp [H, l]; ring
    rw [heq]
    positivity
  let V := 2 * (1 - t ^ 2) ^ 2 + 3 * c * (1 - t ^ 4) +
    c ^ 2 * (t ^ 4 + t ^ 2 + 2)
  have hV : 0 < V := by dsimp [V]; positivity
  have hupp : 0 < H c t U := by
    have heq : H c t U = t ^ 3 * (1 - c) * V / D ^ 2 := by
      dsimp only [H, U]
      field_simp [ne_of_gt hD]
      dsimp only [D, V]
      ring
    rw [heq]
    positivity
  have hslo : l ≤ skew c t := skew_lower c t hc0.le hc1.le ⟨ht.1.le, ht.2⟩
  have hsup : skew c t ≤ U := skew_upper c t hc0.le hc1.le ⟨ht.1.le, ht.2⟩
  let w := (skew c t - l) / (U - l)
  have hw0 : 0 ≤ w := div_nonneg (sub_nonneg.mpr hslo) (sub_pos.mpr hlU).le
  have hw1 : w ≤ 1 := (div_le_one (sub_pos.mpr hlU)).2 (by linarith)
  have hwrepr : skew c t = (1 - w) * l + w * U := by
    dsimp [w]
    field_simp [ne_of_gt (sub_pos.mpr hlU)]
    <;> ring
  have hchord : H c t (skew c t) = (1 - w) * H c t l + w * H c t U +
      2 * c * t * w * (1 - w) * (U - l) ^ 2 := by
    rw [hwrepr]
    dsimp [H]
    ring
  have hextra : 0 ≤ 2 * c * t * w * (1 - w) * (U - l) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) htp.le) hw0)
      (sub_nonneg.mpr hw1)) (sq_nonneg _)
  have hmain : 0 < (1 - w) * H c t l + w * H c t U := by
    by_cases hw : w = 0
    · simpa only [hw, sub_zero, one_mul, zero_mul, add_zero] using hlow
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) hlow.le)
        (mul_pos (lt_of_le_of_ne hw0 (Ne.symm hw)) hupp)
  rw [hchord]
  linarith

private lemma R_mono (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    StrictMonoOn (R c) (Ioo (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1)
  · intro t ht
    exact (R_deriv c t hc0 hc1 ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioo] at ht
    rw [(R_deriv c t hc0 hc1 ht).deriv]
    exact div_pos (mul_pos (mul_pos (by norm_num) hc0) (H_positive c t hc0 hc1 ht))
      (sq_pos_of_pos (R_den_pos c t hc0 hc1 ht))

private lemma R_limit_zero (c : ℝ) : Tendsto (R c) (𝓝[>] (0 : ℝ)) (𝓝 (c * (1 + c) / 2)) := by
  have hsd : HasDerivAt (skew c) c 0 := by
    simpa only [skew_zero, zero_pow (by norm_num : 2 ≠ 0), sub_zero, mul_one, div_one]
      using skew_deriv c 0 ⟨le_rfl, by norm_num⟩
  have hne : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) := nhdsWithin_mono _ (by
    intro t ht
    simpa only [mem_compl_iff, mem_singleton_iff] using ne_of_gt ht)
  have hz : Tendsto (fun t => skew c t / t) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    convert hsd.tendsto_slope.mono_left hne using 1
    funext t
    rw [slope_def_field, skew_zero, sub_zero, sub_zero]
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have hn := (hz.const_add 1).const_mul c
  have hd := (((hid.pow 2).const_sub 1).const_mul 2).add
    (((hid.pow 2).const_mul c).mul (hz.const_add 1))
  have hlim : Tendsto (fun t => c * (1 + skew c t / t) /
      (2 * (1 - t ^ 2) + c * t ^ 2 * (1 + skew c t / t)))
      (𝓝[>] (0 : ℝ)) (𝓝 (c * (1 + c) / 2)) := by
    convert hn.div hd (by norm_num) using 1 <;> first | rfl | norm_num
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  dsimp [R]
  have ht0 : t ≠ 0 := ne_of_gt ht
  field_simp [ht0]
  <;> ring

private lemma R_limit_one (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    Tendsto (R c) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
  let q := fun t => 2 * t * (1 - t ^ 2) / (c * (t + skew c t))
  have hid : Tendsto (fun t : ℝ => t) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have hnear : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Ioo (0 : ℝ) 1 := by
    have hlo : ∀ᶠ t in 𝓝[<] (1 : ℝ), 0 < t :=
      (show ∀ᶠ t in 𝓝 (1 : ℝ), 0 < t from
        Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hlo, self_mem_nhdsWithin] with t ht hlt
    exact ⟨ht, hlt⟩
  have hb : ∀ᶠ t in 𝓝[<] (1 : ℝ), 0 ≤ q t ∧ q t ≤ 2 * (1 - t ^ 2) / c := by
    filter_upwards [hnear] with t ht
    have hs := (skew_basic c t hc0.le hc1.le ⟨ht.1.le, ht.2⟩).1
    have hd : 0 < c * (t + skew c t) := mul_pos hc0 (by linarith [ht.1])
    have hsq : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    dsimp [q]
    constructor
    · exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) ht.1.le) hsq.le) hd.le
    · apply (div_le_div_iff₀ hd hc0).2
      nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * c) hsq.le) hs]
  have hbound : Tendsto (fun t : ℝ => 2 * (1 - t ^ 2) / c)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    convert ((tendsto_const_nhds.sub (hid.pow 2)).const_mul 2).div_const c using 1
      <;> first | rfl | norm_num
  have hq : Tendsto q (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
      (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)
  have hlim : Tendsto (fun t => 1 / (t ^ 2 + q t)) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
    convert tendsto_const_nhds.div ((hid.pow 2).add hq) (by norm_num) using 1
      <;> first | rfl | norm_num
  apply hlim.congr'
  filter_upwards [hnear] with t ht
  have hs := (skew_basic c t hc0.le hc1.le ⟨ht.1.le, ht.2⟩).1
  have hd : c * (t + skew c t) ≠ 0 := ne_of_gt (mul_pos hc0 (by linarith [ht.1]))
  have hts : t + skew c t ≠ 0 := ne_of_gt (by linarith [ht.1])
  have hden := ne_of_gt (R_den_pos c t hc0 hc1 ht)
  dsimp [q, R]
  field_simp [hd, hts, ne_of_gt hc0, ne_of_gt ht.1, hden]
  <;> ring

private lemma R_above_initial (c t : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) : c * (1 + c) / 2 < R c t := by
  have hh : t / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < t / 2 :=
    (show ∀ᶠ s in 𝓝 (0 : ℝ), s < t / 2 from
      Iio_mem_nhds hh.1).filter_mono nhdsWithin_le_nhds
  have hle : c * (1 + c) / 2 ≤ R c (t / 2) := by
    apply le_of_tendsto (R_limit_zero c)
    filter_upwards [hsmall, self_mem_nhdsWithin] with s hs hs0
    exact ((R_mono c hc0 hc1) ⟨hs0, lt_trans hs hh.2⟩ hh hs).le
  exact lt_of_le_of_lt hle ((R_mono c hc0 hc1) hh ht (by linarith [ht.1]))

private lemma R_crossing (a c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (ha : c * (1 + c) / 2 < a) (ha1 : a < 1) :
    ∃ t ∈ Ioo (0 : ℝ) 1, R c t = a := by
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo (0 : ℝ) 1 ∧ R c s < a := by
    have hlo := (R_limit_zero c).eventually (Iio_mem_nhds ha)
    have hs1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 :=
      (show ∀ᶠ s in 𝓝 (0 : ℝ), s < 1 from Iio_mem_nhds (by norm_num)).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [hlo, hs1, self_mem_nhdsWithin] with s hR hs hs0
    exact ⟨⟨hs0, hs⟩, hR⟩
  obtain ⟨s, hs, hsR⟩ := hsmall.exists
  have hlarge : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Ioo (0 : ℝ) 1 ∧ a < R c t := by
    have hhi := (R_limit_one c hc0 hc1).eventually (Ioi_mem_nhds ha1)
    have ht0 : ∀ᶠ t in 𝓝[<] (1 : ℝ), 0 < t :=
      (show ∀ᶠ t in 𝓝 (1 : ℝ), 0 < t from Ioi_mem_nhds (by norm_num)).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [hhi, ht0, self_mem_nhdsWithin] with t hR ht ht1
    exact ⟨⟨ht, ht1⟩, hR⟩
  obtain ⟨t, ht, htR⟩ := hlarge.exists
  have hst : s < t := by
    by_contra hn
    have hle := (R_mono c hc0 hc1).monotoneOn ht hs (le_of_not_gt hn)
    linarith
  have hcont : ContinuousOn (R c) (Icc s t) := by
    intro u hu
    exact (R_deriv c u hc0 hc1 ⟨lt_of_lt_of_le hs.1 hu.1,
      lt_of_le_of_lt hu.2 ht.2⟩).continuousAt.continuousWithinAt
  obtain ⟨u, hu, hur⟩ := intermediate_value_Icc hst.le hcont ⟨hsR.le, htR.le⟩
  exact ⟨u, ⟨lt_of_lt_of_le hs.1 hu.1, lt_of_le_of_lt hu.2 ht.2⟩, hur⟩

private lemma threshold_iff (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    threshold a ≤ c ↔ a ≤ c * (1 + c) / 2 := by
  have hsq := Real.sq_sqrt (show 0 ≤ 1 + 8 * a by linarith)
  have hs := Real.sqrt_nonneg (1 + 8 * a)
  have hc' : 0 ≤ 2 * c + 1 := by linarith
  unfold threshold
  constructor
  · intro h
    have hle : Real.sqrt (1 + 8 * a) ≤ 2 * c + 1 := by linarith
    have hp := mul_self_le_mul_self hs hle
    nlinarith
  · intro h
    by_contra hn
    have hlt : 2 * c + 1 < Real.sqrt (1 + 8 * a) := by linarith
    have hp := mul_self_lt_mul_self hc' hlt
    nlinarith

private def Qt (a c t : ℝ) : ℝ := (1 - a * t ^ 2) * powerCurvature c t

private lemma Qt_cont (a c : ℝ) : ContinuousOn (Qt a c) (Ico (0 : ℝ) 1) := by
  intro t ht
  exact (((continuousAt_const.sub (continuousAt_const.mul (continuousAt_id.pow 2))).mul
    (curvature_hasDerivAt c t ht).continuousAt) : ContinuousAt (Qt a c) t).continuousWithinAt

private lemma Qt_deriv (a c t : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) : HasDerivAt (Qt a c)
      (powerCurvature c t *
        (t * (2 * (1 - t ^ 2) + c * t * (t + skew c t))) /
        (1 - t ^ 2) * (R c t - a)) t := by
  have hraw := (((hasDerivAt_id t).pow 2).const_mul a |>.const_sub 1).mul
    (curvature_hasDerivAt c t ⟨ht.1.le, ht.2⟩)
  convert hraw using 1 <;> try rfl
  simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, show 2 - 1 = (1 : ℕ) by omega,
    pow_one, mul_one]
  unfold R
  have hinner : 2 * (1 - t ^ 2) + c * t * (t + skew c t) ≠ 0 :=
    (mul_ne_zero_iff.mp (ne_of_gt (R_den_pos c t hc0 hc1 ht))).2
  field_simp [ne_of_gt (R_den_pos c t hc0 hc1 ht),
    ne_of_gt ht.1, hinner,
    ne_of_gt (show 0 < 1 - t ^ 2 by nlinarith [ht.1, ht.2])]
  ring_nf at hinner ⊢
  field_simp [hinner]
  <;> ring

private lemma Qt_factor_pos (c t : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < powerCurvature c t *
        (t * (2 * (1 - t ^ 2) + c * t * (t + skew c t))) / (1 - t ^ 2) :=
  div_pos (mul_pos (curvature_pos c t ⟨ht.1.le, ht.2⟩) (R_den_pos c t hc0 hc1 ht))
    (by nlinarith [ht.1, ht.2])

private lemma Qt_increasing (a c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (ha : a ≤ c * (1 + c) / 2) : StrictMonoOn (Qt a c) (Ico (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ico 0 1) (Qt_cont a c)
  intro t ht
  rw [interior_Ico] at ht
  rw [(Qt_deriv a c t hc0 hc1 ht).deriv]
  exact mul_pos (Qt_factor_pos c t hc0 hc1 ht)
    (sub_pos.mpr (lt_of_le_of_lt ha (R_above_initial c t hc0 hc1 ht)))

private lemma Qt_turn (a c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (ha : c * (1 + c) / 2 < a) (ha1 : a < 1) :
    ∃ t ∈ Ioo (0 : ℝ) 1, StrictAntiOn (Qt a c) (Icc 0 t) ∧
      StrictMonoOn (Qt a c) (Ico t 1) := by
  obtain ⟨u, hu, hur⟩ := R_crossing a c hc0 hc1 ha ha1
  refine ⟨u, hu, ?_, ?_⟩
  · apply strictAntiOn_of_deriv_neg (convex_Icc 0 u)
    · exact (Qt_cont a c).mono (by intro t ht; exact ⟨ht.1, lt_of_le_of_lt ht.2 hu.2⟩)
    · intro t ht
      rw [interior_Icc] at ht
      have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, lt_trans ht.2 hu.2⟩
      rw [(Qt_deriv a c t hc0 hc1 ht').deriv]
      apply mul_neg_of_pos_of_neg (Qt_factor_pos c t hc0 hc1 ht')
      have hlt := (R_mono c hc0 hc1) ht' hu ht.2
      rw [hur] at hlt
      linarith
  · apply strictMonoOn_of_deriv_pos (convex_Ico u 1)
    · exact (Qt_cont a c).mono (by intro t ht; exact ⟨le_trans hu.1.le ht.1, ht.2⟩)
    · intro t ht
      rw [interior_Ico] at ht
      have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_trans hu.1 ht.1, ht.2⟩
      rw [(Qt_deriv a c t hc0 hc1 ht').deriv]
      apply mul_pos (Qt_factor_pos c t hc0 hc1 ht')
      have hlt := (R_mono c hc0 hc1) hu ht' ht.1
      rw [hur] at hlt
      linarith

private lemma profile_Qt (a c u : ℝ) (hu : 0 ≤ u) :
    thresholdProfile a c u = Qt a c (Real.sqrt u) := by
  simp only [thresholdProfile, Qt, Real.sq_sqrt hu]

theorem solution : PowerThresholdClaim := by
  intro a c ha ha1 hc hc1
  constructor
  · intro hthr u hu v hv huv
    rw [profile_Qt a c u hu.1, profile_Qt a c v hv.1]
    apply Qt_increasing a c hc hc1 ((threshold_iff a c ha hc).mp hthr)
    · exact ⟨Real.sqrt_nonneg _, (Real.sqrt_lt hu.1 (by norm_num : (0 : ℝ) ≤ 1)).2 (by simpa using hu.2)⟩
    · exact ⟨Real.sqrt_nonneg _, (Real.sqrt_lt hv.1 (by norm_num : (0 : ℝ) ≤ 1)).2 (by simpa using hv.2)⟩
    · exact Real.sqrt_lt_sqrt hu.1 huv
  · intro hthr
    have hinit : c * (1 + c) / 2 < a := lt_of_not_ge (by
      intro h
      exact not_le_of_gt hthr ((threshold_iff a c ha hc).mpr h))
    obtain ⟨t, ht, hanti, hmono⟩ := Qt_turn a c hc hc1 hinit ha1
    refine ⟨t ^ 2, ⟨sq_pos_of_pos ht.1, by nlinarith [ht.1, ht.2]⟩, ?_, ?_⟩
    · intro u hu v hv huv
      rw [profile_Qt a c u hu.1, profile_Qt a c v hv.1]
      apply hanti
      · exact ⟨Real.sqrt_nonneg _, (Real.sqrt_le_left ht.1.le).2 hu.2⟩
      · exact ⟨Real.sqrt_nonneg _, (Real.sqrt_le_left ht.1.le).2 hv.2⟩
      · exact Real.sqrt_lt_sqrt hu.1 huv
    · intro u hu v hv huv
      have hu0 : 0 ≤ u := le_trans (sq_nonneg t) hu.1
      have hv0 : 0 ≤ v := le_trans (sq_nonneg t) hv.1
      rw [profile_Qt a c u hu0, profile_Qt a c v hv0]
      apply hmono
      · exact ⟨(Real.le_sqrt ht.1.le hu0).2 hu.1,
          (Real.sqrt_lt hu0 (by norm_num : (0 : ℝ) ≤ 1)).2 (by simpa using hu.2)⟩
      · exact ⟨(Real.le_sqrt ht.1.le hv0).2 hv.1,
          (Real.sqrt_lt hv0 (by norm_num : (0 : ℝ) ≤ 1)).2 (by simpa using hv.2)⟩
      · exact Real.sqrt_lt_sqrt hu0 huv


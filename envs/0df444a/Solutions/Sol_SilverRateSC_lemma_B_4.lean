-- Prove2me | solution 1 for SilverRateSC.lemma_B_4
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T18:28:40.310231+00:00
-- url     : https://prove2.me/submissions/e3f99634-2108-4d7d-a9e6-9d3e797a9331

import Mathlib
import Definitions.Def_SilverRateSC_pOf

namespace SolSilverRateB4

open Real Set

/-- The function `f(z) = z^p + (1-z)^p + c z^p (1-z)^p`. -/
noncomputable def F (p c z : ℝ) : ℝ := z ^ p + (1 - z) ^ p + c * z ^ p * (1 - z) ^ p

/-- The sign factor `g(z) = (1-z)^{1-p} - z^{1-p} + c(1-2z)` of `f'`. -/
noncomputable def g (p c z : ℝ) : ℝ := (1 - z) ^ (1 - p) - z ^ (1 - p) + c * (1 - 2 * z)

/-- `g'`. -/
noncomputable def g1 (p c z : ℝ) : ℝ := (p - 1) * (1 - z) ^ (-p) + (p - 1) * z ^ (-p) - 2 * c

/-- `g''`. -/
noncomputable def g2 (p z : ℝ) : ℝ := (p - 1) * p * ((1 - z) ^ (-p - 1) - z ^ (-p - 1))

theorem F_symm (p c z : ℝ) : F p c (1 - z) = F p c z := by
  unfold F; rw [sub_sub_cancel]; ring

theorem hasDerivAt_F (p c z : ℝ) (hp : 1 < p) (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (F p c) (p * z ^ (p - 1) * (1 - z) ^ (p - 1) * g p c z) z := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ p) (1 * p * z ^ (p - 1)) z :=
    (hasDerivAt_id z).rpow_const (Or.inl hz0.ne')
  have h2 : HasDerivAt (fun y : ℝ => (1 - y) ^ p) ((0 - 1) * p * (1 - z) ^ (p - 1)) z :=
    ((hasDerivAt_const z (1:ℝ)).sub (hasDerivAt_id z)).rpow_const (Or.inl (by simp; linarith))
  have hA : z ^ p = z * z ^ (p - 1) := by
    conv_lhs => rw [show p = 1 + (p - 1) by ring]
    rw [rpow_add hz0, rpow_one]
  have hB : (1 - z) ^ p = (1 - z) * (1 - z) ^ (p - 1) := by
    conv_lhs => rw [show p = 1 + (p - 1) by ring]
    rw [rpow_add (by linarith), rpow_one]
  have hA' : z ^ (1 - p) = (z ^ (p - 1))⁻¹ := by
    rw [← rpow_neg hz0.le]; ring_nf
  have hB' : (1 - z) ^ (1 - p) = ((1 - z) ^ (p - 1))⁻¹ := by
    rw [← rpow_neg (by linarith)]; ring_nf
  have hApos : 0 < z ^ (p - 1) := rpow_pos_of_pos hz0 _
  have hBpos : 0 < (1 - z) ^ (p - 1) := rpow_pos_of_pos (by linarith) _
  refine ((h1.add h2).add ((h1.const_mul c).mul h2)).congr_deriv ?_
  unfold g
  rw [hA', hB', hA, hB]
  field_simp
  ring

theorem hasDerivAt_g (p c z : ℝ) (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (g p c) (g1 p c z) z := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ (1 - p)) (1 * (1 - p) * z ^ (1 - p - 1)) z :=
    (hasDerivAt_id z).rpow_const (Or.inl hz0.ne')
  have h2 : HasDerivAt (fun y : ℝ => (1 - y) ^ (1 - p)) ((0 - 1) * (1 - p) * (1 - z) ^ (1 - p - 1)) z :=
    ((hasDerivAt_const z (1:ℝ)).sub (hasDerivAt_id z)).rpow_const (Or.inl (by simp; linarith))
  have h3 : HasDerivAt (fun y : ℝ => c * (1 - 2 * y)) (c * (0 - 2 * 1)) z :=
    ((hasDerivAt_const z (1:ℝ)).sub ((hasDerivAt_id z).const_mul 2)).const_mul c
  refine ((h2.sub h1).add h3).congr_deriv ?_
  unfold g1
  rw [show (1 : ℝ) - p - 1 = -p by ring]
  ring

theorem hasDerivAt_g1 (p c z : ℝ) (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (g1 p c) (g2 p z) z := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ (-p)) (1 * (-p) * z ^ (-p - 1)) z :=
    (hasDerivAt_id z).rpow_const (Or.inl hz0.ne')
  have h2 : HasDerivAt (fun y : ℝ => (1 - y) ^ (-p)) ((0 - 1) * (-p) * (1 - z) ^ (-p - 1)) z :=
    ((hasDerivAt_const z (1:ℝ)).sub (hasDerivAt_id z)).rpow_const (Or.inl (by simp; linarith))
  refine (((h2.const_mul (p - 1)).add (h1.const_mul (p - 1))).sub_const (2 * c)).congr_deriv ?_
  unfold g2; ring

theorem g_concave (p c : ℝ) (hp : 1 < p) : ConcaveOn ℝ (Ioc 0 (1/2)) (g p c) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ioc 0 (1/2)) (f' := g1 p c) (f'' := g2 p)
  · intro z hz
    exact (hasDerivAt_g p c z hz.1 (by linarith [hz.2])).continuousAt.continuousWithinAt
  · intro z hz
    rw [interior_Ioc] at hz
    exact (hasDerivAt_g p c z hz.1 (by linarith [hz.2])).hasDerivWithinAt
  · intro z hz
    rw [interior_Ioc] at hz
    exact (hasDerivAt_g1 p c z hz.1 (by linarith [hz.2])).hasDerivWithinAt
  · intro z hz
    rw [interior_Ioc] at hz
    unfold g2
    have : (1 - z) ^ (-p - 1) ≤ z ^ (-p - 1) :=
      rpow_le_rpow_of_nonpos hz.1 (by linarith [hz.2]) (by linarith)
    have hpp : 0 ≤ (p - 1) * p := by nlinarith
    nlinarith

theorem F_continuousOn (p c : ℝ) (hp : 0 < p) : ContinuousOn (F p c) (Icc 0 1) := by
  have h1 : ContinuousOn (fun y : ℝ => y ^ p) (Icc 0 1) :=
    continuousOn_id.rpow_const (fun _ _ => Or.inr hp.le)
  have h2 : ContinuousOn (fun y : ℝ => (1 - y) ^ p) (Icc 0 1) :=
    (continuousOn_const.sub continuousOn_id).rpow_const (fun _ _ => Or.inr hp.le)
  exact (h1.add h2).add ((continuousOn_const.mul h1).mul h2)

/-- `f(z) ≤ 1` on `[0, 1/2]`, given `f(1/2) = 1`. -/
theorem F_le_one_half (p c : ℝ) (hp : 1 < p) (hhalf : F p c (1/2) = 1) (z : ℝ)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1/2) : F p c z ≤ 1 := by
  have hp0 : 0 < p := by linarith
  have hF0 : F p c 0 = 1 := by
    unfold F; rw [zero_rpow hp0.ne']; simp
  rcases eq_or_lt_of_le hz0 with h0 | hzpos
  · rw [← h0, hF0]
  rcases eq_or_lt_of_le hz1 with h1 | hzlt
  · rw [h1, hhalf]
  have hconc := g_concave p c hp
  have hghalf : g p c (1/2) = 0 := by unfold g; norm_num
  have hderiv : ∀ w, 0 < w → w < 1 →
      HasDerivAt (F p c) (p * w ^ (p - 1) * (1 - w) ^ (p - 1) * g p c w) w :=
    fun w h1 h2 => hasDerivAt_F p c w hp h1 h2
  have hpos : ∀ w, 0 < w → w < 1 → 0 < p * w ^ (p - 1) * (1 - w) ^ (p - 1) := fun w h1 h2 =>
    mul_pos (mul_pos hp0 (rpow_pos_of_pos h1 _)) (rpow_pos_of_pos (by linarith) _)
  have hcont : ∀ a b : ℝ, 0 ≤ a → b ≤ 1 → ContinuousOn (F p c) (Icc a b) := fun a b ha hb =>
    (F_continuousOn p c hp0).mono (Icc_subset_Icc ha hb)
  by_cases hgz : 0 ≤ g p c z
  · -- `g ≥ 0` on `[z, 1/2]`, so `f` increases there
    have hgpos : ∀ w ∈ Icc z (1/2), 0 ≤ g p c w := by
      intro w hw
      have := hconc.ge_on_segment (x := z) (y := 1/2) ⟨hzpos, hz1⟩ ⟨by norm_num, le_rfl⟩
        (by rw [segment_eq_Icc hz1]; exact hw)
      rw [hghalf] at this
      exact le_trans (le_min hgz le_rfl) this
    have hmono : MonotoneOn (F p c) (Icc z (1/2)) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) (hcont _ _ hz0 (by norm_num))
        (f' := fun w => p * w ^ (p - 1) * (1 - w) ^ (p - 1) * g p c w)
      · intro w hw
        rw [interior_Icc] at hw
        exact (hderiv w (by linarith [hw.1]) (by linarith [hw.2])).hasDerivWithinAt
      · intro w hw
        rw [interior_Icc] at hw
        exact mul_nonneg (hpos w (by linarith [hw.1]) (by linarith [hw.2])).le
          (hgpos w ⟨hw.1.le, hw.2.le⟩)
    have := hmono ⟨le_rfl, hz1⟩ ⟨hz1, le_rfl⟩ hz1
    rw [hhalf] at this
    exact this
  · -- `g ≤ 0` on `(0, z]`, so `f` decreases on `[0, z]`
    rw [not_le] at hgz
    have hgneg : ∀ w, 0 < w → w ≤ z → g p c w ≤ 0 := by
      intro w hw0 hwz
      by_contra hcon
      rw [not_le] at hcon
      have := hconc.ge_on_segment (x := w) (y := 1/2) ⟨hw0, by linarith⟩ ⟨by norm_num, le_rfl⟩
        (z := z) (by rw [segment_eq_Icc (by linarith)]; exact ⟨hwz, hz1⟩)
      rw [hghalf] at this
      have : min (g p c w) 0 = 0 := min_eq_right hcon.le
      linarith
    have hanti : AntitoneOn (F p c) (Icc 0 z) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) (hcont _ _ le_rfl (by linarith))
        (f' := fun w => p * w ^ (p - 1) * (1 - w) ^ (p - 1) * g p c w)
      · intro w hw
        rw [interior_Icc] at hw
        exact (hderiv w hw.1 (by linarith [hw.2])).hasDerivWithinAt
      · intro w hw
        rw [interior_Icc] at hw
        exact mul_nonpos_of_nonneg_of_nonpos (hpos w hw.1 (by linarith [hw.2])).le
          (hgneg w hw.1 hw.2.le)
    have := hanti ⟨le_rfl, hz0⟩ ⟨hz0, le_rfl⟩ hz0
    rw [hF0] at this
    exact this

theorem F_le_one (p c : ℝ) (hp : 1 < p) (hhalf : F p c (1/2) = 1) (z : ℝ)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : F p c z ≤ 1 := by
  rcases le_total z (1/2) with h | h
  · exact F_le_one_half p c hp hhalf z hz0 h
  · rw [← F_symm]
    exact F_le_one_half p c hp hhalf (1 - z) (by linarith) (by linarith)

end SolSilverRateB4

open SilverRateSC SolSilverRateB4 Real in
theorem solution (a c x y B : ℝ) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) (ha : 8 ≤ a) (hx : a ≤ x)
    (hy : a ≤ y) (hB : 0 < B) (hW : (x + y + B - a) * B = c * x * y) :
    (x + y + B - a) ^ (1 / pOf c) ≤ x ^ (1 / pOf c) + y ^ (1 / pOf c) := by
  set K : ℝ := 1 + √(1 + c) with hKdef
  have hs1 : 1 < √(1 + c) := by
    rw [Real.lt_sqrt (by norm_num)]; linarith
  have hK2 : 2 < K := by linarith
  have hsq : √(1 + c) ^ 2 = 1 + c := Real.sq_sqrt (by linarith)
  have hcK : c = K ^ 2 - 2 * K := by rw [hKdef]; nlinarith
  set p := pOf c with hpdef
  have h2p : (2:ℝ) ^ p = K := by
    rw [hpdef, pOf]; exact Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
  have hp : 1 < p := by
    have : (2:ℝ) ^ (1:ℝ) < 2 ^ p := by rw [rpow_one, h2p]; exact hK2
    exact (rpow_lt_rpow_left_iff (by norm_num)).1 this
  have hp0 : 0 < p := by linarith
  have hhalf : F p c (1/2) = 1 := by
    have e : ((1:ℝ)/2) ^ p = K⁻¹ := by
      rw [one_div, inv_rpow (by norm_num), h2p]
    unfold F
    rw [show (1:ℝ) - 1/2 = 1/2 by norm_num, e, hcK]
    field_simp
    ring
  -- notation
  have hxpos : 0 < x := by linarith
  have hypos : 0 < y := by linarith
  set ν : ℝ := 1 / p with hν
  have hνp : ν = p⁻¹ := by rw [hν, one_div]
  have hxν : 0 < x ^ ν := rpow_pos_of_pos hxpos _
  have hyν : 0 < y ^ ν := rpow_pos_of_pos hypos _
  set S := x ^ ν + y ^ ν with hS
  have hSpos : 0 < S := by linarith
  set M := S ^ p with hM
  have hMpos : 0 < M := rpow_pos_of_pos hSpos _
  set z := x ^ ν / S with hz
  have hz0 : 0 ≤ z := by positivity
  have hz1 : z ≤ 1 := by rw [hz, div_le_one hSpos]; linarith
  have h1z : 1 - z = y ^ ν / S := by rw [hz]; field_simp; ring
  have hzp : z ^ p = x / M := by
    rw [hz, div_rpow hxν.le hSpos.le, hνp, rpow_inv_rpow hxpos.le hp0.ne']
  have h1zp : (1 - z) ^ p = y / M := by
    rw [h1z, div_rpow hyν.le hSpos.le, hνp, rpow_inv_rpow hypos.le hp0.ne']
  have key := F_le_one p c hp hhalf z hz0 hz1
  unfold F at key
  rw [hzp, h1zp] at key
  have hQM : x * M + y * M + c * x * y ≤ M ^ 2 := by
    have e : (x / M + y / M + c * (x / M) * (y / M)) * M ^ 2 = x * M + y * M + c * x * y := by
      field_simp
    have := mul_le_mul_of_nonneg_right key (sq_nonneg M)
    rw [e, one_mul] at this
    exact this
  -- `W ≤ M`
  set W := x + y + B - a with hWdef
  have hWpos : 0 < W := by rw [hWdef]; linarith
  have hWM : W ≤ M := by
    by_contra hcon
    rw [not_le] at hcon
    have hMxy : x + y < M := by
      by_contra h'
      rw [not_lt] at h'
      have : 0 < c * x * y := by positivity
      nlinarith
    have hQW : W ^ 2 - (x + y) * W - c * x * y = -a * W := by
      rw [← hW, hWdef]; ring
    have : 0 < (W - M) * (W + M - (x + y)) := mul_pos (by linarith) (by linarith)
    nlinarith
  calc W ^ ν ≤ M ^ ν := rpow_le_rpow hWpos.le hWM (by rw [hν]; positivity)
    _ = S := by rw [hM, hνp, rpow_rpow_inv hSpos.le hp0.ne']

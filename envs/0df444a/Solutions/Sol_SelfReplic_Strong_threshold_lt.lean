-- Prove2me | solution 1 for SelfReplic.Strong.threshold_lt
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T03:06:09.113748+00:00
-- url     : https://prove2.me/submissions/70279989-83f7-4fcf-a842-fb9e9e607416

import Mathlib
import Definitions.Def_SelfReplic_Strong_Model

open MeasureTheory Set SelfReplic.Strong

namespace SRThr

/-- FTC for a function given in integral form on `[0,T]` with continuous integrand. -/
lemma hasDerivWithinAt_of_integral {F g : ℝ → ℝ} {c T : ℝ} (hT : 0 ≤ T)
    (hg : ContinuousOn g (Icc 0 T))
    (hF : ∀ t ∈ Icc 0 T, F t = c + ∫ u in (0:ℝ)..t, g u) :
    ∀ t ∈ Ico 0 T, HasDerivWithinAt F (g t) (Ici t) t := by
  intro t ht
  set g' : ℝ → ℝ := fun u => g (projIcc 0 T hT u) with hg'
  have hcont : Continuous g' := by
    apply hg.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    intro u; exact (projIcc 0 T hT u).2
  have heq : ∀ v ∈ Icc 0 T, F v = c + ∫ u in (0:ℝ)..v, g' u := by
    intro v hv
    rw [hF v hv]
    congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hv.1] at hu
    simp only [hg']
    rw [projIcc_of_mem hT ⟨hu.1, hu.2.trans hv.2⟩]
  have hd : HasDerivAt (fun v => c + ∫ u in (0:ℝ)..v, g' u) (g' t) t := by
    have := hcont.integral_hasStrictDerivAt 0 t
    exact this.hasDerivAt.const_add c
  have hgt : g' t = g t := by
    simp only [hg']; rw [projIcc_of_mem hT ⟨ht.1, ht.2.le⟩]
  rw [← hgt]
  apply hd.hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [Ico_mem_nhdsGE ht.2] with v hv
    exact heq v ⟨ht.1.trans hv.1, hv.2.le⟩
  · exact heq t ⟨ht.1, ht.2.le⟩

lemma withIL_d (P : Params) (J : ℝ) (x : Traj) : x.d (P.withIL J) = x.d P := rfl

lemma d_continuousOn (P : Params) (x : Traj) {A : Set ℝ} (hD : ContinuousOn x.D A)
    (hS : ContinuousOn x.S A) : ContinuousOn (x.d P) A := by
  unfold Traj.d demandRate
  exact (continuousOn_const.add ((continuousOn_const.mul hS).div_const _)).mul
    (continuousOn_const.sub hD)

lemma key_lip (a b m Sx Sy Dx Dy B N : ℝ) (hSx : |Sx| ≤ B) (hDy : |Dy| ≤ B)
    (hN1 : |Dx - Dy| ≤ N) (hN2 : |Sx - Sy| ≤ N) :
    |(a + b * Sx / m) * (m - Dx) - (a + b * Sy / m) * (m - Dy)| ≤
      (|a| + |b / m| * B + |b / m| * (|m| + B)) * N := by
  have hN : 0 ≤ N := (abs_nonneg _).trans hN1
  have hB : 0 ≤ B := (abs_nonneg _).trans hSx
  have hab : 0 ≤ |a| + |b / m| * B := by positivity
  have h1 : |a + b / m * Sx| ≤ |a| + |b / m| * B := by
    calc |a + b / m * Sx| ≤ |a| + |b / m * Sx| := abs_add_le _ _
      _ = |a| + |b / m| * |Sx| := by rw [abs_mul]
      _ ≤ |a| + |b / m| * B := by gcongr
  have h2 : |m - Dy| ≤ |m| + B := (abs_sub _ _).trans (by gcongr)
  have h3 : |Dy - Dx| ≤ N := by rw [abs_sub_comm]; exact hN1
  calc |(a + b * Sx / m) * (m - Dx) - (a + b * Sy / m) * (m - Dy)|
      = |(a + b / m * Sx) * (Dy - Dx) + b / m * (Sx - Sy) * (m - Dy)| := by
        congr 1; ring
    _ ≤ |a + b / m * Sx| * |Dy - Dx| + |b / m| * |Sx - Sy| * |m - Dy| := by
        rw [← abs_mul, ← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ (|a| + |b / m| * B) * N + |b / m| * N * (|m| + B) := by gcongr
    _ = (|a| + |b / m| * B + |b / m| * (|m| + B)) * N := by ring

/-- Uniqueness for the sales-always-on demand system `D' = d`, `S' = d - wS`. -/
lemma salesOn_unique (P : Params) (hT : 0 ≤ P.T) (x y : Traj)
    (hxD : ContinuousOn x.D (Icc 0 P.T)) (hxS : ContinuousOn x.S (Icc 0 P.T))
    (hyD : ContinuousOn y.D (Icc 0 P.T)) (hyS : ContinuousOn y.S (Icc 0 P.T))
    (hx : ∀ t ∈ Icc 0 P.T, x.D t = 0 + ∫ u in (0:ℝ)..t, x.d P u ∧
        x.S t = 0 + ∫ u in (0:ℝ)..t, (x.d P u - P.w * x.S u))
    (hy : ∀ t ∈ Icc 0 P.T, y.D t = 0 + ∫ u in (0:ℝ)..t, y.d P u ∧
        y.S t = 0 + ∫ u in (0:ℝ)..t, (y.d P u - P.w * y.S u)) :
    ∀ t ∈ Icc 0 P.T, x.D t = y.D t ∧ x.S t = y.S t := by
  obtain ⟨B1, hB1⟩ := isCompact_Icc.exists_bound_of_continuousOn hxS
  obtain ⟨B2, hB2⟩ := isCompact_Icc.exists_bound_of_continuousOn hyD
  set B := max B1 B2
  set L := |P.alpha| + |P.beta / P.m| * B + |P.beta / P.m| * (|P.m| + B)
  have hxd := d_continuousOn P x hxD hxS
  have hyd := d_continuousOn P y hyD hyS
  have dxD := hasDerivWithinAt_of_integral hT hxd (fun t ht => (hx t ht).1)
  have dxS := hasDerivWithinAt_of_integral hT (hxd.sub (continuousOn_const.mul hxS))
    (fun t ht => (hx t ht).2)
  have dyD := hasDerivWithinAt_of_integral hT hyd (fun t ht => (hy t ht).1)
  have dyS := hasDerivWithinAt_of_integral hT (hyd.sub (continuousOn_const.mul hyS))
    (fun t ht => (hy t ht).2)
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := fun t => (x.D t - y.D t, x.S t - y.S t))
    (f' := fun t => (x.d P t - y.d P t, (x.d P t - P.w * x.S t) - (y.d P t - P.w * y.S t)))
    (K := L + |P.w|) (a := 0) (b := P.T)
    ((hxD.sub hyD).prodMk (hxS.sub hyS))
    (fun t ht => ((dxD t ht).sub (dyD t ht)).prodMk ((dxS t ht).sub (dyS t ht)))
    (by
      have h0 := hx 0 ⟨le_refl _, hT⟩
      have h0' := hy 0 ⟨le_refl _, hT⟩
      simp only [intervalIntegral.integral_same, add_zero] at h0 h0'
      simp [h0.1, h0.2, h0'.1, h0'.2])
    (by
      intro t ht
      have htI : t ∈ Icc 0 P.T := ⟨ht.1, ht.2.le⟩
      have hSx : |x.S t| ≤ B := by
        have := hB1 t htI; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
      have hDy : |y.D t| ≤ B := by
        have := hB2 t htI; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_right _ _)
      set N := ‖(x.D t - y.D t, x.S t - y.S t)‖
      have hN1 : |x.D t - y.D t| ≤ N := by
        simp only [N, Prod.norm_def, Real.norm_eq_abs]; exact le_max_left _ _
      have hN2 : |x.S t - y.S t| ≤ N := by
        simp only [N, Prod.norm_def, Real.norm_eq_abs]; exact le_max_right _ _
      have hN : 0 ≤ N := norm_nonneg _
      have hk := key_lip P.alpha P.beta P.m (x.S t) (y.S t) (x.D t) (y.D t) B N hSx hDy hN1 hN2
      have hk' : |x.d P t - y.d P t| ≤ L * N := hk
      have hB0 : 0 ≤ B := (abs_nonneg _).trans hSx
      have hL : 0 ≤ L := by positivity
      simp only [Prod.norm_def, Real.norm_eq_abs]
      apply max_le
      · nlinarith [abs_nonneg P.w]
      · calc |x.d P t - P.w * x.S t - (y.d P t - P.w * y.S t)|
            = |(x.d P t - y.d P t) - P.w * (x.S t - y.S t)| := by ring_nf
          _ ≤ |x.d P t - y.d P t| + |P.w * (x.S t - y.S t)| := abs_sub _ _
          _ ≤ L * N + |P.w| * N := by rw [abs_mul]; gcongr
          _ = (L + |P.w|) * N := by ring)
  intro t ht
  have := hz t ht
  simp only [Prod.mk_eq_zero, sub_eq_zero] at this
  exact this

lemma salesOn_form (P : Params) (J : ℝ) (x : Traj) (hx : IsAdmissible (P.withIL J) x)
    (hs : SalesAlwaysOn (P.withIL J) x) :
    ∀ t ∈ Icc 0 P.T, x.D t = 0 + ∫ u in (0:ℝ)..t, x.d P u ∧
        x.S t = 0 + ∫ u in (0:ℝ)..t, (x.d P u - P.w * x.S u) := by
  intro t ht
  obtain ⟨-, -, -, -, -, hode, -⟩ := hx
  obtain ⟨h1, h2, -⟩ := hode t ht
  refine ⟨by rw [zero_add]; exact h1, ?_⟩
  rw [zero_add, h2]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht.1] at hu
  simp only
  rw [hs u ⟨hu.1, hu.2.trans ht.2⟩]
  rfl

end SRThr

open SRThr in
theorem solution (P : Params) (hP : P.Standing) (hSR : P.StrongRepl)
    (Ilow Ihigh : ℝ)
    (hlow : IsLowLevel P Ilow) (hhigh : IsHighLevel P Ihigh) :
    Ilow < Ihigh := by
  have hT : 0 < P.T := hP.2.2.2.2.2.2.1
  have hr : 0 < P.r := by linarith [hP.2.2.1, hP.2.2.2.1]
  have hTm : P.T ∈ Icc 0 P.T := ⟨hT.le, le_refl _⟩
  obtain ⟨x, hxa, hxp, hxs, hxIT0, hxpos⟩ := hlow
  obtain ⟨y, hya, hyp, hys, hyIT0, -⟩ := hhigh
  have fx := salesOn_form P Ilow x hxa hxs
  have fy := salesOn_form P Ihigh y hya hys
  obtain ⟨-, -, hxD, hxS, hxI, hxode, -, -⟩ := hxa
  obtain ⟨-, -, hyD, hyS, -, hyode, -, -⟩ := hya
  have hu := salesOn_unique P hT.le x y hxD hxS hyD hyS fx fy
  have hxd := d_continuousOn P x hxD hxS
  have hyd := d_continuousOn P y hyD hyS
  have hxdi : IntervalIntegrable (x.d P) volume 0 P.T :=
    hxd.intervalIntegrable_of_Icc hT.le
  have hydi : IntervalIntegrable (y.d P) volume 0 P.T :=
    hyd.intervalIntegrable_of_Icc hT.le
  have hxIi : IntervalIntegrable x.I volume 0 P.T := hxI.intervalIntegrable_of_Icc hT.le
  -- high level
  have hHigh : Ihigh = y.D P.T := by
    have h1 := (hyode P.T hTm).2.2
    have h2 : ∫ u in (0:ℝ)..P.T, (y.p u - y.s u) = ∫ u in (0:ℝ)..P.T, (-(y.d P u)) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hT.le] at hu
      simp only
      rw [hyp u hu, hys u hu]
      simp [withIL_d]
    rw [h2, intervalIntegral.integral_neg] at h1
    have h3 := (fy P.T hTm).1
    change y.I P.T = 0 at hyIT0
    change y.I P.T = Ihigh + -∫ u in (0:ℝ)..P.T, y.d P u at h1
    linarith
  have hLow : Ilow = x.D P.T - P.r * ∫ u in (0:ℝ)..P.T, x.I u := by
    have h1 := (hxode P.T hTm).2.2
    have h2 : ∫ u in (0:ℝ)..P.T, (x.p u - x.s u) =
        ∫ u in (0:ℝ)..P.T, (P.r * x.I u - x.d P u) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hT.le] at hu
      simp only
      rw [hxp u hu, hxs u hu]
      rfl
    rw [h2, intervalIntegral.integral_sub (hxIi.const_mul _) hxdi,
      intervalIntegral.integral_const_mul] at h1
    have h3 := (fx P.T hTm).1
    change x.I P.T = 0 at hxIT0
    change x.I P.T = Ilow + (P.r * (∫ u in (0:ℝ)..P.T, x.I u) - ∫ u in (0:ℝ)..P.T, x.d P u) at h1
    linarith
  have hpos : 0 < ∫ u in (0:ℝ)..P.T, x.I u :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hxIi
      (fun u hu => hxpos u ⟨hu.1.le, hu.2⟩) hT
  have hDD := (hu P.T hTm).1
  rw [hLow, hHigh, ← hDD]
  have := mul_pos hr hpos
  linarith

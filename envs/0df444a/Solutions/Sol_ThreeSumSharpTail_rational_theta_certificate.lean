-- Prove2me | solution 1 for ThreeSumSharpTail.rational_theta_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-13T17:51:06.422568+00:00
-- url     : https://prove2.me/submissions/32121d9a-351d-4fab-8ca2-5f6e2bca140a

import Definitions.Def_ThreeSumSharpTail_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ThreeSumSharpTail

private theorem entropy_continuousAt {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ContinuousAt entropy x := by
  unfold entropy
  have hlogx : ContinuousAt (fun y : ℝ => Real.log y) x :=
    Real.continuousAt_log (ne_of_gt hx0)
  have hcomp : ContinuousAt (fun y : ℝ => 1 - y) x :=
    continuousAt_const.sub continuousAt_id
  have hlogcomp : ContinuousAt (fun y : ℝ => Real.log (1 - y)) x :=
    (Real.continuousAt_log (ne_of_gt (sub_pos.mpr hx1))).comp hcomp
  exact (continuousAt_id.neg.mul hlogx).sub (hcomp.mul hlogcomp)

private theorem sharpSaving_continuousAt (c : ℝ) (hc : 10 < c) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10) :
    ContinuousAt (fun t : ℝ => sharpSaving c t) θ := by
  have hcpos : 0 < c := by linarith
  have harg0 : 0 < 1 / c := by positivity
  have harg1 : 1 / c < 1 := by
    rw [div_lt_one hcpos]
    linarith
  have hθcomp0 : 0 < 1 - θ := by linarith
  have hθcomp1 : 1 - θ < c := by linarith
  have hscaled0 : 0 < (1 - θ) / c := div_pos hθcomp0 hcpos
  have hscaled1 : (1 - θ) / c < 1 := (div_lt_one hcpos).2 hθcomp1
  have hscaled : ContinuousAt (fun t : ℝ => (1 - t) / c) θ := by
    exact (continuousAt_const.sub continuousAt_id).div_const c
  have hentScaled : ContinuousAt (fun t : ℝ => entropy ((1 - t) / c)) θ := by
    exact ContinuousAt.comp (f := fun t : ℝ => (1 - t) / c) (g := entropy) (x := θ)
      (entropy_continuousAt (x := (1 - θ) / c) hscaled0 hscaled1) hscaled
  have hfirst : ContinuousAt (fun _ : ℝ => c * entropy (1 / c)) θ := continuousAt_const
  have hsecond : ContinuousAt (fun t : ℝ => c * entropy ((1 - t) / c)) θ :=
    continuousAt_const.mul hentScaled
  have hthird : ContinuousAt (fun t : ℝ => t * Real.log 9) θ :=
    continuousAt_id.mul continuousAt_const
  unfold sharpSaving
  exact ((hfirst.sub hsecond).sub hthird).div_const (Real.log 4)

private theorem queryExponent_continuousAt {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ContinuousAt queryExponent θ := by
  have hent := entropy_continuousAt hθ0 hθ1
  have hprod : ContinuousAt (fun t : ℝ => t * Real.log 9) θ :=
    continuousAt_id.mul continuousAt_const
  unfold queryExponent
  exact (hent.add hprod).div_const (Real.log 4)

/-- Strict real feasibility persists at a nearby rational parameter. -/
theorem solution (c : ℕ) (θ : ℝ) (a s : ℚ)
    (hc : 10 < c) (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10)
    (henc : (a : ℝ) * (encodingExponent c + sharpSaving c θ) < 1)
    (hprep : (s : ℝ) < sharpSaving c θ)
    (hquery : (s : ℝ) < 1 / 2 - queryExponent θ) :
    ∃ η : ℚ, 0 < (η : ℝ) ∧ (η : ℝ) < 9 / 10 ∧
      (a : ℝ) * (encodingExponent c + sharpSaving c (η : ℝ)) < 1 ∧
      (s : ℝ) < sharpSaving c (η : ℝ) ∧
      (s : ℝ) < 1 / 2 - queryExponent (η : ℝ) := by
  let encFun : ℝ → ℝ := fun t => (a : ℝ) * (encodingExponent c + sharpSaving c t) - 1
  let prepFun : ℝ → ℝ := fun t => (s : ℝ) - sharpSaving c t
  let queryFun : ℝ → ℝ := fun t => (s : ℝ) + queryExponent t - 1 / 2
  have hcReal : 10 < (c : ℝ) := by exact_mod_cast hc
  have hθ1 : θ < 1 := by linarith
  have hencAt : encFun θ < 0 := by dsimp [encFun]; linarith
  have hprepAt : prepFun θ < 0 := by dsimp [prepFun]; linarith
  have hqueryAt : queryFun θ < 0 := by dsimp [queryFun]; linarith
  have hencCont : ContinuousAt encFun θ := by
    dsimp [encFun]
    exact continuousAt_const.mul (continuousAt_const.add
      (sharpSaving_continuousAt (c : ℝ) hcReal hθ0 hθ9)) |>.sub continuousAt_const
  have hprepCont : ContinuousAt prepFun θ := by
    dsimp [prepFun]
    exact continuousAt_const.sub (sharpSaving_continuousAt (c : ℝ) hcReal hθ0 hθ9)
  have hqueryCont : ContinuousAt queryFun θ := by
    dsimp [queryFun]
    exact (continuousAt_const.add (queryExponent_continuousAt hθ0 hθ1)).sub continuousAt_const
  have hencNhds := hencCont.preimage_mem_nhds (isOpen_Iio.mem_nhds hencAt)
  have hprepNhds := hprepCont.preimage_mem_nhds (isOpen_Iio.mem_nhds hprepAt)
  have hqueryNhds := hqueryCont.preimage_mem_nhds (isOpen_Iio.mem_nhds hqueryAt)
  rcases Metric.mem_nhds_iff.mp hencNhds with ⟨εenc, hεenc, hballEnc⟩
  rcases Metric.mem_nhds_iff.mp hprepNhds with ⟨εprep, hεprep, hballPrep⟩
  rcases Metric.mem_nhds_iff.mp hqueryNhds with ⟨εquery, hεquery, hballQuery⟩
  let δ : ℝ := min εenc (min εprep (min εquery (min θ (9 / 10 - θ))))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδenc : δ ≤ εenc := by dsimp [δ]; exact min_le_left _ _
  have hδprep : δ ≤ εprep := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδquery : δ ≤ εquery := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδtheta : δ ≤ θ := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hδupper : δ ≤ 9 / 10 - θ := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn (show θ - δ < θ + δ by linarith)
  refine ⟨q, ?_, ?_, ?_, ?_, ?_⟩
  · have hdist : |(q : ℝ) - θ| < δ := by rw [abs_lt]; constructor <;> linarith
    linarith [hqlo]
  · have hdist : |(q : ℝ) - θ| < δ := by rw [abs_lt]; constructor <;> linarith
    linarith [hqhi]
  · have hdist : dist (q : ℝ) θ < εenc := by
      rw [Real.dist_eq]
      exact lt_of_lt_of_le (by rw [abs_sub_comm]; exact abs_lt.mpr ⟨by linarith [hqlo], by linarith [hqhi]⟩) hδenc
    have hmem : (q : ℝ) ∈ Metric.ball θ εenc := Metric.mem_ball.mpr hdist
    have := hballEnc hmem
    change encFun (q : ℝ) < 0 at this
    dsimp [encFun] at this
    linarith
  · have hdist : dist (q : ℝ) θ < εprep := by
      rw [Real.dist_eq]
      exact lt_of_lt_of_le (by rw [abs_sub_comm]; exact abs_lt.mpr ⟨by linarith [hqlo], by linarith [hqhi]⟩) hδprep
    have hmem : (q : ℝ) ∈ Metric.ball θ εprep := Metric.mem_ball.mpr hdist
    have := hballPrep hmem
    change prepFun (q : ℝ) < 0 at this
    dsimp [prepFun] at this
    linarith
  · have hdist : dist (q : ℝ) θ < εquery := by
      rw [Real.dist_eq]
      exact lt_of_lt_of_le (by rw [abs_sub_comm]; exact abs_lt.mpr ⟨by linarith [hqlo], by linarith [hqhi]⟩) hδquery
    have hmem : (q : ℝ) ∈ Metric.ball θ εquery := Metric.mem_ball.mpr hdist
    have := hballQuery hmem
    change queryFun (q : ℝ) < 0 at this
    dsimp [queryFun] at this
    linarith

#print axioms solution

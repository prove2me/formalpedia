-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P18.deltaOne_strictAntiOn_and_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Imine
-- created : 2026-10-21T01:44:17.19368+00:00
-- url     : https://prove2.me/submissions/7516dc9f-baab-4812-9d0b-2e1d30093660

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P18
noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open QAlgorithms.Papers.Independent.Next46.P18 (deltaOne)

-- import the g/phi lemmas from ScratchDerivPhi by copy (abbreviated)
private lemma deriv_g {x : ℝ} (hx : 0 < x) :
    deriv g x = Real.log (x + 1) - Real.log x := by
  unfold g
  have hx1 : x + 1 ≠ 0 := by positivity
  have h1 : deriv (fun y : ℝ => (y + 1) * Real.log (y + 1)) x =
      Real.log (x + 1) + 1 := by
    change deriv ((fun y : ℝ => y + 1) * (fun y : ℝ => Real.log (y + 1))) x =
      Real.log (x + 1) + 1
    rw [deriv_mul]
    · have hinner : HasDerivAt (fun y : ℝ => y + 1) 1 x := by
        simpa using (hasDerivAt_id x).add_const 1
      have hlog : deriv (fun y : ℝ => Real.log (y + 1)) x = (x + 1)⁻¹ := by
        simpa using (hinner.log hx1).deriv
      rw [hlog]
      simp only [deriv_add_const, deriv_id'', one_mul]
      field_simp [hx1]
    · fun_prop
    · fun_prop
  have h2 : deriv (fun y : ℝ => y * Real.log y) x = Real.log x + 1 := by
    rw [Real.deriv_mul_log hx.ne']
  change deriv ((fun y : ℝ => (y + 1) * Real.log (y + 1)) -
    (fun y : ℝ => y * Real.log y)) x = Real.log (x + 1) - Real.log x
  rw [deriv_sub]
  · rw [h1, h2]
    ring
  · fun_prop
  · fun_prop

private lemma differentiableAt_g {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ g x := by
  have hpos : 0 < Real.log (x + 1) - Real.log x :=
    sub_pos.mpr (Real.log_lt_log hx (by linarith))
  exact differentiableAt_of_deriv_ne_zero (by rw [deriv_g hx]; exact ne_of_gt hpos)

private lemma deriv_phi {t : ℝ} (ht : 1 / 2 < t) :
    deriv (fun s : ℝ => g (s - 1 / 2)) t =
      Real.log (t + 1 / 2) - Real.log (t - 1 / 2) := by
  change deriv (g ∘ fun s : ℝ => s - 1 / 2) t = _
  rw [deriv_comp]
  · rw [deriv_g (by linarith : 0 < t - 1 / 2)]
    rw [show t - 1 / 2 + 1 = t + 1 / 2 by ring]
    simp
  · exact differentiableAt_g (by linarith : 0 < t - 1 / 2)
  · fun_prop

private lemma differentiableAt_phi {t : ℝ} (ht : 1 / 2 < t) :
    DifferentiableAt ℝ (fun s : ℝ => g (s - 1 / 2)) t := by
  have h : DifferentiableAt ℝ g (t - 1 / 2) := differentiableAt_g (by linarith)
  exact DifferentiableAt.comp t h (by fun_prop : DifferentiableAt ℝ (fun s : ℝ => s - 1 / 2) t)

private lemma deriv_sqrt_affine {E c P : ℝ} (h : 0 < E * P + c) :
    deriv (fun P : ℝ => Real.sqrt (E * P + c)) P = E / (2 * Real.sqrt (E * P + c)) := by
  have hlin : HasDerivAt (fun P : ℝ => E * P + c) E P := by
    simpa using ((hasDerivAt_id P).const_mul E).const_add c
  exact (hlin.sqrt (ne_of_gt h)).deriv

private lemma differentiableAt_sqrt_affine {E c P : ℝ} (h : 0 < E * P + c) :
    DifferentiableAt ℝ (fun P : ℝ => Real.sqrt (E * P + c)) P := by
  exact (Real.hasDerivAt_sqrt (ne_of_gt h)).differentiableAt.comp P (by fun_prop)

private lemma sqrt_one_div_four : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
  rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

private lemma deriv_sqrt_linear {E P : ℝ} (h : 0 < E * P) :
    deriv (fun P : ℝ => Real.sqrt (E * P)) P = E / (2 * Real.sqrt (E * P)) := by
  have h' : 0 < E * P + 0 := by simpa using h
  simpa using deriv_sqrt_affine (c := 0) h'

private lemma differentiableAt_sqrt_linear {E P : ℝ} (h : 0 < E * P) :
    DifferentiableAt ℝ (fun P : ℝ => Real.sqrt (E * P)) P := by
  have h' : 0 < E * P + 0 := by simpa using h
  simpa using differentiableAt_sqrt_affine (c := 0) h'

private lemma deriv_deltaOne {E v P : ℝ} (hE : 0 < E) (hv : 0 < v)
    (hP : 1 / (4 * E) < P) :
    deriv (deltaOne E v) P =
      (E / (2 * Real.sqrt (E * P + E / (4 * v)))) *
        (Real.log (Real.sqrt (E * P + E / (4 * v)) + 1 / 2) -
          Real.log (Real.sqrt (E * P + E / (4 * v)) - 1 / 2)) -
      (E / (2 * Real.sqrt (E * P))) *
        (Real.log (Real.sqrt (E * P) + 1 / 2) - Real.log (Real.sqrt (E * P) - 1 / 2)) := by
  unfold deltaOne
  let a := Real.sqrt (E * P + E / (4 * v))
  let b := Real.sqrt (E * P)
  have hc : 0 < E / (4 * v) := by positivity
  have hb_pos : 0 < E * P := by
    have h4E : 0 < 4 * E := by positivity
    have h1 : 1 < P * (4 * E) := (div_lt_iff₀ h4E).mp hP
    nlinarith
  have hEP : (1 / 4 : ℝ) < E * P := by
    have h4E : 0 < 4 * E := by positivity
    have h1 : 1 < P * (4 * E) := (div_lt_iff₀ h4E).mp hP
    nlinarith
  have ha_pos : 0 < E * P + E / (4 * v) := by positivity
  have ha : 1 / 2 < a := by
    dsimp [a]
    have hlt : (1 / 4 : ℝ) < E * P + E / (4 * v) := by linarith
    have := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 4) hlt
    rwa [sqrt_one_div_four] at this
  have hb : 1 / 2 < b := by
    dsimp [b]
    have hlt : (1 / 4 : ℝ) < E * P := hEP
    have := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 4) hlt
    rwa [sqrt_one_div_four] at this
  have hf : deriv (fun P : ℝ => g (Real.sqrt (E * P + E / (4 * v)) - 1 / 2)) P =
      (E / (2 * Real.sqrt (E * P + E / (4 * v)))) *
        (Real.log (Real.sqrt (E * P + E / (4 * v)) + 1 / 2) -
          Real.log (Real.sqrt (E * P + E / (4 * v)) - 1 / 2)) := by
    change deriv ((fun t : ℝ => g (t - 1 / 2)) ∘
      fun P : ℝ => Real.sqrt (E * P + E / (4 * v))) P = _
    rw [deriv_comp]
    · rw [deriv_phi ha, deriv_sqrt_affine ha_pos]
      dsimp [a]
      ring
    · exact differentiableAt_phi ha
    · exact differentiableAt_sqrt_affine ha_pos
  have hg : deriv (fun P : ℝ => g (Real.sqrt (E * P) - 1 / 2)) P =
      (E / (2 * Real.sqrt (E * P))) *
        (Real.log (Real.sqrt (E * P) + 1 / 2) -
          Real.log (Real.sqrt (E * P) - 1 / 2)) := by
    change deriv ((fun t : ℝ => g (t - 1 / 2)) ∘
      fun P : ℝ => Real.sqrt (E * P)) P = _
    rw [deriv_comp]
    · rw [deriv_phi hb, deriv_sqrt_linear hb_pos]
      dsimp [b]
      ring
    · exact differentiableAt_phi hb
    · exact differentiableAt_sqrt_linear hb_pos
  change deriv ((fun P : ℝ => g (Real.sqrt (E * P + E / (4 * v)) - 1 / 2)) -
    (fun P : ℝ => g (Real.sqrt (E * P) - 1 / 2))) P = _
  rw [deriv_sub]
  · rw [hf, hg]
  · exact DifferentiableAt.comp P (differentiableAt_phi ha) (differentiableAt_sqrt_affine ha_pos)
  · exact DifferentiableAt.comp P (differentiableAt_phi hb) (differentiableAt_sqrt_linear hb_pos)

def H (t : ℝ) : ℝ :=
  (Real.log (t + 1 / 2) - Real.log (t - 1 / 2)) / t

private lemma deriv_log_shift {t : ℝ} (ht : 1 / 2 < t) :
    deriv (fun s : ℝ => Real.log (s + 1 / 2)) t = 1 / (t + 1 / 2) := by
  change deriv (Real.log ∘ fun s : ℝ => s + 1 / 2) t = _
  rw [deriv_comp]
  · rw [Real.deriv_log]
    simp
  · exact Real.differentiableAt_log (by positivity : t + 1 / 2 ≠ 0)
  · fun_prop

private lemma deriv_log_shift' {t : ℝ} (ht : 1 / 2 < t) :
    deriv (fun s : ℝ => Real.log (s - 1 / 2)) t = 1 / (t - 1 / 2) := by
  change deriv (Real.log ∘ fun s : ℝ => s - 1 / 2) t = _
  rw [deriv_comp]
  · rw [Real.deriv_log]
    simp
  · exact Real.differentiableAt_log (by linarith : t - 1 / 2 ≠ 0)
  · fun_prop

private lemma differentiableAt_log_shift {t : ℝ} (ht : 1 / 2 < t) :
    DifferentiableAt ℝ (fun s : ℝ => Real.log (s + 1 / 2)) t :=
  DifferentiableAt.comp t (Real.differentiableAt_log (by positivity : t + 1 / 2 ≠ 0))
    (by fun_prop : DifferentiableAt ℝ (fun s : ℝ => s + 1 / 2) t)

private lemma differentiableAt_log_shift' {t : ℝ} (ht : 1 / 2 < t) :
    DifferentiableAt ℝ (fun s : ℝ => Real.log (s - 1 / 2)) t :=
  DifferentiableAt.comp t (Real.differentiableAt_log (by linarith : t - 1 / 2 ≠ 0))
    (by fun_prop : DifferentiableAt ℝ (fun s : ℝ => s - 1 / 2) t)

private lemma deriv_n {t : ℝ} (ht : 1 / 2 < t) :
    deriv (fun s : ℝ => Real.log (s + 1 / 2) - Real.log (s - 1 / 2)) t =
      1 / (t + 1 / 2) - 1 / (t - 1 / 2) := by
  change deriv ((fun s : ℝ => Real.log (s + 1 / 2)) -
    (fun s : ℝ => Real.log (s - 1 / 2))) t = _
  rw [deriv_sub]
  · rw [deriv_log_shift ht, deriv_log_shift' ht]
  · exact differentiableAt_log_shift ht
  · exact differentiableAt_log_shift' ht

private lemma deriv_H {t : ℝ} (ht : 1 / 2 < t) :
    deriv H t = ((1 / (t + 1 / 2) - 1 / (t - 1 / 2)) * t -
      (Real.log (t + 1 / 2) - Real.log (t - 1 / 2))) / t ^ 2 := by
  unfold H
  change deriv ((fun s : ℝ => Real.log (s + 1 / 2) - Real.log (s - 1 / 2)) /
    (fun s : ℝ => s)) t = _
  rw [deriv_div]
  · rw [deriv_n ht]
    simp
  · exact (differentiableAt_log_shift ht).sub (differentiableAt_log_shift' ht)
  · fun_prop
  · exact ne_of_gt (by linarith : 0 < t)

private lemma continuousOn_log_shift : ContinuousOn (fun s : ℝ => Real.log (s + 1 / 2))
    (Set.Ioi (1 / 2)) := by
  apply ContinuousOn.log
  · fun_prop
  · intro x hx
    have hx' : (1 / 2 : ℝ) < x := hx
    linarith

private lemma continuousOn_log_shift' : ContinuousOn (fun s : ℝ => Real.log (s - 1 / 2))
    (Set.Ioi (1 / 2)) := by
  apply ContinuousOn.log
  · fun_prop
  · intro x hx
    have hx' : (1 / 2 : ℝ) < x := hx
    linarith

private lemma continuousOn_H : ContinuousOn H (Set.Ioi (1 / 2)) := by
  unfold H
  apply ContinuousOn.div
  · exact continuousOn_log_shift.sub continuousOn_log_shift'
  · fun_prop
  · intro x hx
    have hx' : (1 / 2 : ℝ) < x := hx
    linarith

private lemma deriv_H_neg {t : ℝ} (ht : 1 / 2 < t) : deriv H t < 0 := by
  rw [deriv_H ht]
  have htpos : 0 < t := by linarith
  have hA : 1 / (t + 1 / 2) - 1 / (t - 1 / 2) < 0 := by
    have h1 : 1 / (t + 1 / 2) < 1 / (t - 1 / 2) := by
      apply one_div_lt_one_div_of_lt (by linarith : (0 : ℝ) < t - 1 / 2)
      linarith
    linarith
  have hB : 0 < Real.log (t + 1 / 2) - Real.log (t - 1 / 2) := by
    apply sub_pos.mpr
    exact Real.log_lt_log (by linarith : (0 : ℝ) < t - 1 / 2) (by linarith)
  have hnum : (1 / (t + 1 / 2) - 1 / (t - 1 / 2)) * t -
      (Real.log (t + 1 / 2) - Real.log (t - 1 / 2)) < 0 := by
    nlinarith [mul_neg_of_neg_of_pos hA htpos, hB]
  exact div_neg_of_neg_of_pos hnum (by positivity)

private lemma strictAntiOn_H : StrictAntiOn H (Set.Ioi (1 / 2)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi (1 / 2)) continuousOn_H ?_
  intro x hx
  rw [interior_Ioi] at hx
  exact deriv_H_neg hx

private lemma continuousOn_g : ContinuousOn g (Set.Ici (0 : ℝ)) := by
  unfold g
  fun_prop

private lemma continuousOn_phi : ContinuousOn (fun t : ℝ => g (t - 1 / 2)) (Set.Ici (1 / 2)) := by
  apply continuousOn_g.comp
  · fun_prop
  · intro x hx
    have hx' : (1 / 2 : ℝ) ≤ x := hx
    show (0 : ℝ) ≤ x - 1 / 2
    linarith

private lemma continuousOn_sqrt_affine {E c : ℝ} (hE : 0 < E) :
    ContinuousOn (fun P : ℝ => Real.sqrt (E * P + c)) (Set.Ici (1 / (4 * E))) := by
  fun_prop

private lemma deriv_deltaOne_neg {E v P : ℝ} (hE : 0 < E) (hv : 0 < v)
    (hP : 1 / (4 * E) < P) : deriv (deltaOne E v) P < 0 := by
  rw [deriv_deltaOne hE hv hP]
  let a := Real.sqrt (E * P + E / (4 * v))
  let b := Real.sqrt (E * P)
  have hb_pos : 0 < E * P := by
    have h4E : 0 < 4 * E := by positivity
    have h1 : 1 < P * (4 * E) := (div_lt_iff₀ h4E).mp hP
    nlinarith
  have hEP : (1 / 4 : ℝ) < E * P := by
    have h4E : 0 < 4 * E := by positivity
    have h1 : 1 < P * (4 * E) := (div_lt_iff₀ h4E).mp hP
    nlinarith
  have ha : 1 / 2 < a := by
    dsimp [a]
    have hlt : (1 / 4 : ℝ) < E * P + E / (4 * v) := by
      have hc : 0 < E / (4 * v) := by positivity
      linarith
    have := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 4) hlt
    rwa [sqrt_one_div_four] at this
  have hb : 1 / 2 < b := by
    dsimp [b]
    have := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 4) hEP
    rwa [sqrt_one_div_four] at this
  have hba : b < a := by
    dsimp [a, b]
    apply Real.sqrt_lt_sqrt (by positivity : (0 : ℝ) ≤ E * P)
    have hc : 0 < E / (4 * v) := by positivity
    linarith
  have hH : H a < H b := strictAntiOn_H hb ha hba
  have hD : (E / (2 * Real.sqrt (E * P + E / (4 * v)))) *
        (Real.log (Real.sqrt (E * P + E / (4 * v)) + 1 / 2) -
          Real.log (Real.sqrt (E * P + E / (4 * v)) - 1 / 2)) -
      (E / (2 * Real.sqrt (E * P))) *
        (Real.log (Real.sqrt (E * P) + 1 / 2) - Real.log (Real.sqrt (E * P) - 1 / 2)) =
      (E / 2) * (H a - H b) := by
    dsimp [a, b, H]
    ring
  rw [hD]
  exact mul_neg_of_pos_of_neg (by positivity) (sub_neg.mpr hH)

private lemma strictAntiOn_deltaOne {E v : ℝ} (hE : 0 < E) (hv : 0 < v) :
    StrictAntiOn (deltaOne E v) (Set.Ici (1 / (4 * E))) := by
  have hc : 0 < E / (4 * v) := by positivity
  refine strictAntiOn_of_deriv_neg (convex_Ici _) ?_ ?_
  · unfold deltaOne
    apply ContinuousOn.sub
    · refine continuousOn_phi.comp (continuousOn_sqrt_affine (c := E / (4 * v)) hE) ?_
      intro x hx
      have hx' : 1 / (4 * E) ≤ x := hx
      have h4E : 0 < 4 * E := by positivity
      have h1 : 1 ≤ x * (4 * E) := (div_le_iff₀ h4E).mp hx'
      have hEP : (1 / 4 : ℝ) ≤ E * x := by nlinarith
      have h1' : (1 / 2 : ℝ) ≤ Real.sqrt (E * x) := by
        have := Real.sqrt_le_sqrt hEP
        rwa [sqrt_one_div_four] at this
      have hle : E * x ≤ E * x + E / (4 * v) := by linarith
      exact le_trans h1' (Real.sqrt_le_sqrt hle)
    · refine continuousOn_phi.comp (by simpa using continuousOn_sqrt_affine (c := 0) hE) ?_
      intro x hx
      have hx' : 1 / (4 * E) ≤ x := hx
      have h4E : 0 < 4 * E := by positivity
      have h1 : 1 ≤ x * (4 * E) := (div_le_iff₀ h4E).mp hx'
      have hEP : (1 / 4 : ℝ) ≤ E * x := by nlinarith
      have := Real.sqrt_le_sqrt hEP
      rwa [sqrt_one_div_four] at this
  · intro x hx
    rw [interior_Ici] at hx
    exact deriv_deltaOne_neg hE hv hx

private lemma strictAntiOn_deriv_g : StrictAntiOn (fun x : ℝ => deriv g x) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : 0 < x := hx
  have hy' : 0 < y := hy
  change deriv g y < deriv g x
  rw [deriv_g hx', deriv_g hy']
  have hx0 : x ≠ 0 := ne_of_gt hx'
  have hy0 : y ≠ 0 := ne_of_gt hy'
  have h1 : 0 < (y + 1) * x := by positivity
  have h2 : (y + 1) * x < (x + 1) * y := by nlinarith
  have hlog := Real.log_lt_log h1 h2
  rw [Real.log_mul (by positivity : y + 1 ≠ 0) hx0,
    Real.log_mul (by positivity : x + 1 ≠ 0) hy0] at hlog
  linarith

private lemma deltaOne_le_of_one_le {E v P : ℝ} (hE : 0 < E) (hv : 0 < v)
    (hP1 : 1 / (4 * E) ≤ P) (hP2 : 1 ≤ E * P) :
    deltaOne E v P ≤ 1 / (2 * v * P) := by
  let a := Real.sqrt (E * P + E / (4 * v))
  let b := Real.sqrt (E * P)
  let A := a - 1 / 2
  let B := b - 1 / 2
  let c := E / (4 * v)
  have hc : 0 < c := by positivity
  have hbpos : 0 < b := by dsimp [b]; positivity
  have hb1 : 1 ≤ b := by
    dsimp [b]
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hP2
  have hBpos : 0 < B := by dsimp [B]; linarith
  have hBA : B < A := by
    dsimp [A, B, a, b, c]
    apply sub_lt_sub_right
    apply Real.sqrt_lt_sqrt (by positivity)
    linarith
  have hcont : ContinuousOn g (Set.Icc B A) := by
    apply continuousOn_g.mono
    intro x hx
    have hx' : b - 1 / 2 ≤ x := hx.1
    exact le_trans (le_of_lt hBpos) hx'
  have hdiff : DifferentiableOn ℝ g (Set.Ioo B A) := by
    intro x hx
    exact (differentiableAt_g (by linarith [hx.1])).differentiableWithinAt
  obtain ⟨ξ, hξ, hderiv⟩ := exists_deriv_eq_slope g hBA hcont hdiff
  have hξB : B < ξ := hξ.1
  have hderiv_lt : deriv g ξ < deriv g B :=
    strictAntiOn_deriv_g (by linarith : 0 < B) (by linarith : 0 < ξ) hξB
  have hderivB_le : deriv g B ≤ 1 / B := by
    rw [deriv_g hBpos]
    have hlog : Real.log (B + 1) - Real.log B = Real.log (1 + 1 / B) := by
      rw [← Real.log_div (by positivity : B + 1 ≠ 0) (ne_of_gt hBpos)]
      congr 1
      field_simp [ne_of_gt hBpos]
    rw [hlog]
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 1 / B)
    linarith
  have hABpos : 0 < A - B := by linarith
  have hmain : g A - g B ≤ (A - B) / B := by
    have hga : g A - g B = deriv g ξ * (A - B) := by
      have := hderiv
      field_simp [ne_of_gt hABpos] at this ⊢
      linarith
    calc
      g A - g B = deriv g ξ * (A - B) := hga
      _ ≤ (1 / B) * (A - B) := by
        apply mul_le_mul_of_nonneg_right
        · exact le_trans (le_of_lt hderiv_lt) hderivB_le
        · exact le_of_lt hABpos
      _ = (A - B) / B := by ring
  have hsep : A - B = c / (a + b) := by
    have ha2 : a ^ 2 = E * P + c := by
      dsimp [a, c]
      rw [Real.sq_sqrt (by positivity)]
    have hb2 : b ^ 2 = E * P := by
      dsimp [b]
      rw [Real.sq_sqrt (by positivity)]
    have hsum : 0 < a + b := by positivity
    dsimp [A, B]
    field_simp [ne_of_gt hsum]
    nlinarith
  have hle1 : A - B ≤ c / b := by
    rw [hsep]
    exact div_le_div_of_nonneg_left (le_of_lt hc) hbpos (by linarith)
  have hBhalf : b / 2 ≤ B := by dsimp [B]; linarith
  have hle2 : (A - B) / B ≤ (c / b) / (b / 2) := by
    exact div_le_div₀ (by positivity) hle1 (by positivity) hBhalf
  have hb2 : b ^ 2 = E * P := by
    dsimp [b]
    rw [Real.sq_sqrt (by positivity)]
  have hPpos : 0 < P := by
    have hEPpos : 0 < E * P := by linarith
    exact pos_of_mul_pos_right hEPpos (le_of_lt hE)
  have hfinal : (c / b) / (b / 2) = 1 / (2 * v * P) := by
    calc
      (c / b) / (b / 2) = 2 * c / b ^ 2 := by
        field_simp [ne_of_gt hbpos]
      _ = 1 / (2 * v * P) := by
        rw [hb2]
        dsimp [c]
        field_simp [ne_of_gt hE, ne_of_gt hv, ne_of_gt hPpos]
        ring
  change g A - g B ≤ 1 / (2 * v * P)
  calc
    g A - g B ≤ (A - B) / B := hmain
    _ ≤ (c / b) / (b / 2) := hle2
    _ = 1 / (2 * v * P) := hfinal

private lemma strictMonoOn_g : StrictMonoOn g (Set.Ici (0 : ℝ)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) continuousOn_g ?_
  intro x hx
  rw [interior_Ici] at hx
  rw [deriv_g hx]
  exact sub_pos.mpr (Real.log_lt_log hx (by linarith))

private lemma deltaOne_pos {E v P : ℝ} (hE : 0 < E) (hv : 0 < v)
    (hP : 1 / (4 * E) ≤ P) : 0 < deltaOne E v P := by
  unfold deltaOne
  apply sub_pos.mpr
  have h4E : 0 < 4 * E := by positivity
  have h1 : 1 ≤ P * (4 * E) := (div_le_iff₀ h4E).mp hP
  have hEP : (1 / 4 : ℝ) ≤ E * P := by nlinarith
  have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt (E * P) := by
    have := Real.sqrt_le_sqrt hEP
    rwa [sqrt_one_div_four] at this
  have hsecond : (0 : ℝ) ≤ Real.sqrt (E * P) - 1 / 2 := by linarith
  have hpos : 0 < E / (4 * v) := by positivity
  have hlt : Real.sqrt (E * P) - 1 / 2 < Real.sqrt (E * P + E / (4 * v)) - 1 / 2 := by
    have hlt0 : E * P < E * P + E / (4 * v) := by linarith
    have := Real.sqrt_lt_sqrt (by positivity : (0 : ℝ) ≤ E * P) hlt0
    linarith
  have hfirst : (0 : ℝ) ≤ Real.sqrt (E * P + E / (4 * v)) - 1 / 2 := by linarith
  exact strictMonoOn_g hsecond hfirst hlt

private lemma tendsto_deltaOne {E v : ℝ} (hE : 0 < E) (hv : 0 < v) :
    Tendsto (deltaOne E v) atTop (𝓝 0) := by
  have hlow : ∀ᶠ P : ℝ in atTop, 0 ≤ deltaOne E v P := by
    filter_upwards [eventually_ge_atTop (1 / (4 * E))] with P hP
    exact le_of_lt (deltaOne_pos hE hv hP)
  have hupp : ∀ᶠ P : ℝ in atTop, deltaOne E v P ≤ ((2 * v) * P)⁻¹ := by
    filter_upwards [eventually_ge_atTop (1 / E)] with P hP
    have hP1 : 1 / (4 * E) ≤ P := by
      have h4E : 0 < 4 * E := by positivity
      have h1 : 1 / (4 * E) ≤ 1 / E := by
        apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hE
        linarith
      exact le_trans h1 hP
    have hP2 : 1 ≤ E * P := by
      have h1 : 1 ≤ P * E := (div_le_iff₀ hE).mp hP
      linarith
    simpa [one_div] using deltaOne_le_of_one_le hE hv hP1 hP2
  have hden : Tendsto (fun P : ℝ => (2 * v) * P) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity : 0 < 2 * v) tendsto_id
  have hlim : Tendsto (fun P : ℝ => ((2 * v) * P)⁻¹) atTop (𝓝 0) :=
    hden.inv_tendsto_atTop
  exact squeeze_zero' hlow hupp hlim



theorem solution {E v : ℝ} (hE : 0 < E) (hv : 0 < v) :
    StrictAntiOn (deltaOne E v) (Set.Ici (1 / (4 * E))) ∧
    Tendsto (deltaOne E v) atTop (𝓝 0) :=
  ⟨strictAntiOn_deltaOne hE hv, tendsto_deltaOne hE hv⟩

end

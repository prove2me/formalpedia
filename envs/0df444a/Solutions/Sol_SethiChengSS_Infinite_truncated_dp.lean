-- Prove2me | solution 1 for SethiChengSS.Infinite.truncated_dp
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:45:11.409737+00:00
-- url     : https://prove2.me/submissions/2ceba359-79bd-474e-b24c-f526cf4ad187

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Infinite_Model

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SethiChengSS.Infinite.TruncDP

open SethiChengSS.Infinite

variable {L : ℕ}

/-! ### Section 1: Standing assumptions, Lipschitz surplus cost, and `Fnext` regularity -/

lemma P_nonneg {D : Model L} (hD : Standing D) (i j : Fin L) : 0 ≤ D.P i j := hD.1 i j
lemma P_sum {D : Model L} (hD : Standing D) (i : Fin L) : ∑ j, D.P i j = 1 := hD.2.1 i
lemma φ_meas {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) : Measurable (D.φ k i) :=
  hD.2.2.1 k i
lemma φ_nonneg {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) (z : ℝ) : 0 ≤ D.φ k i z :=
  hD.2.2.2.1 k i z
lemma φ_neg {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) (z : ℝ) (hz : z < 0) :
    D.φ k i z = 0 := hD.2.2.2.2.1 k i z hz
lemma φ_lint {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) :
    ∫⁻ z, ENNReal.ofReal (D.φ k i z) = 1 := hD.2.2.2.2.2.1 k i
lemma φ_mean_lint {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) :
    ∫⁻ z, ENNReal.ofReal (z * D.φ k i z) ≤ ENNReal.ofReal D.M := hD.2.2.2.2.2.2.1 k i
lemma K_nonneg {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) : 0 ≤ D.K k i :=
  hD.2.2.2.2.2.2.2.1 k i
lemma c_nonneg {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) : 0 ≤ D.c k i :=
  hD.2.2.2.2.2.2.2.2.1 k i
lemma f_convex {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) :
    ConvexOn ℝ Set.univ (D.f k i) := hD.2.2.2.2.2.2.2.2.2.1 k i
lemma f_nonneg {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) (x : ℝ) : 0 ≤ D.f k i x :=
  hD.2.2.2.2.2.2.2.2.2.2.1 k i x
lemma C_pos {D : Model L} (hD : Standing D) : 0 < D.C :=
  hD.2.2.2.2.2.2.2.2.2.2.2.2.1
lemma f_growth {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) (x : ℝ) :
    D.f k i x ≤ D.C * (1 + |x|) := hD.2.2.2.2.2.2.2.2.2.2.2.2.2 k i x

lemma delta_nonneg (z : ℝ) : 0 ≤ delta z := by
  unfold delta; split_ifs <;> norm_num

lemma delta_zero : delta 0 = 0 := by
  unfold delta; simp

lemma delta_pos {z : ℝ} (hz : 0 < z) : delta z = 1 := by
  unfold delta; simp [hz]

lemma orderCost_nonneg {D : Model L} (hD : Standing D) {k : ℕ} {i : Fin L} {u : ℝ}
    (hu : 0 ≤ u) : 0 ≤ orderCost D k i u :=
  add_nonneg (mul_nonneg (K_nonneg hD k i) (delta_nonneg u))
    (mul_nonneg (c_nonneg hD k i) hu)

lemma orderCost_zero (D : Model L) (k : ℕ) (i : Fin L) : orderCost D k i 0 = 0 := by
  simp [orderCost, delta_zero]

lemma orderCost_pos (D : Model L) (k : ℕ) (i : Fin L) {u : ℝ} (hu : 0 < u) :
    orderCost D k i u = D.K k i + D.c k i * u := by
  simp [orderCost, delta_pos hu]

lemma continuous_of_convex_univ {g : ℝ → ℝ} (hg : ConvexOn ℝ Set.univ g) : Continuous g := by
  have := hg.continuousOn_interior
  rw [interior_univ] at this
  exact continuousOn_univ.mp this

lemma f_continuous {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) :
    Continuous (D.f k i) := continuous_of_convex_univ (f_convex hD k i)

lemma f_lipschitz_sub {D : Model L} (hD : Standing D) (k : ℕ) (j : Fin L) (a b : ℝ) :
    D.f k j b - D.f k j a ≤ D.C * |b - a| := by
  have hconv := f_convex hD k j
  have hnn := f_nonneg hD k j
  have hgr := f_growth hD k j
  have hC := C_pos hD
  rcases lt_trichotomy a b with hab | hab | hab
  · have hkey : ∀ t : ℝ, 0 < t → D.f k j b - D.f k j a ≤ (b - a) * (D.C * ((1 + |b|) / t + 1)) := by
      intro t ht
      have hs := hconv.slope_mono_adjacent (x := a) (y := b) (z := b + t) trivial trivial hab
        (by linarith)
      have e1 : b + t - b = t := by ring
      rw [e1] at hs
      have h1 : (D.f k j b - D.f k j a) ≤ (b - a) * ((D.f k j (b + t) - D.f k j b) / t) := by
        rw [div_le_iff₀ (by linarith)] at hs
        rw [mul_comm]; exact hs
      have h2 : (D.f k j (b + t) - D.f k j b) / t ≤ D.C * ((1 + |b|) / t + 1) := by
        rw [div_le_iff₀ ht]
        have := hgr (b + t); have := hnn b
        have : |b + t| ≤ |b| + t := by
          calc |b + t| ≤ |b| + |t| := abs_add_le _ _
            _ = |b| + t := by rw [abs_of_pos ht]
        have e : D.C * ((1 + |b|) / t + 1) * t = D.C * (1 + |b|) + D.C * t := by field_simp
        rw [e]; nlinarith
      calc D.f k j b - D.f k j a ≤ (b - a) * ((D.f k j (b + t) - D.f k j b) / t) := h1
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by linarith)
    have hlim : Tendsto (fun t : ℝ => (b - a) * (D.C * ((1 + |b|) / t + 1))) atTop
        (𝓝 ((b - a) * (D.C * (0 + 1)))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.mul
        ((tendsto_const_nhds.div_atTop tendsto_id).add tendsto_const_nhds))
    have := ge_of_tendsto hlim ((eventually_gt_atTop 0).mono fun t ht => hkey t ht)
    rw [abs_of_pos (by linarith : 0 < b - a)]
    linarith
  · subst hab; simp
  · have hkey : ∀ t : ℝ, 0 < t → D.f k j b - D.f k j a ≤ (a - b) * (D.C * ((1 + |b|) / t + 1)) := by
      intro t ht
      have hs := hconv.slope_mono_adjacent (x := b - t) (y := b) (z := a) trivial trivial
        (by linarith) hab
      have e1 : b - (b - t) = t := by ring
      rw [e1] at hs
      have h1 : D.f k j b - D.f k j a ≤ (a - b) * ((D.f k j (b - t) - D.f k j b) / t) := by
        have h3 : (D.f k j b - D.f k j (b - t)) / t * (a - b) ≤ D.f k j a - D.f k j b := by
          have := mul_le_mul_of_nonneg_right hs (by linarith : 0 ≤ a - b)
          rwa [div_mul_cancel₀ _ (by linarith : (a - b) ≠ 0)] at this
        have e : (a - b) * ((D.f k j (b - t) - D.f k j b) / t) =
            -((D.f k j b - D.f k j (b - t)) / t * (a - b)) := by ring
        rw [e]; linarith
      have h2 : (D.f k j (b - t) - D.f k j b) / t ≤ D.C * ((1 + |b|) / t + 1) := by
        rw [div_le_iff₀ ht]
        have := hgr (b - t); have := hnn b
        have : |b - t| ≤ |b| + t := by
          calc |b - t| ≤ |b| + |t| := abs_sub _ _
            _ = |b| + t := by rw [abs_of_pos ht]
        have e : D.C * ((1 + |b|) / t + 1) * t = D.C * (1 + |b|) + D.C * t := by field_simp
        rw [e]; nlinarith
      calc D.f k j b - D.f k j a ≤ (a - b) * ((D.f k j (b - t) - D.f k j b) / t) := h1
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by linarith)
    have hlim : Tendsto (fun t : ℝ => (a - b) * (D.C * ((1 + |b|) / t + 1))) atTop
        (𝓝 ((a - b) * (D.C * (0 + 1)))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.mul
        ((tendsto_const_nhds.div_atTop tendsto_id).add tendsto_const_nhds))
    have := ge_of_tendsto hlim ((eventually_gt_atTop 0).mono fun t ht => hkey t ht)
    rw [abs_of_neg (by linarith : b - a < 0)]
    linarith

lemma f_lipschitz {D : Model L} (hD : Standing D) (k : ℕ) (j : Fin L) (a b : ℝ) :
    |D.f k j b - D.f k j a| ≤ D.C * |b - a| := by
  rw [abs_le]
  constructor
  · have := f_lipschitz_sub hD k j b a
    rw [abs_sub_comm] at this
    linarith
  · exact f_lipschitz_sub hD k j a b

lemma lintegral_Ioi_eq_lintegral {g : ℝ → ℝ≥0∞} (hg : ∀ z < 0, g z = 0) :
    ∫⁻ z in Set.Ioi (0 : ℝ), g z = ∫⁻ z, g z := by
  rw [← lintegral_indicator measurableSet_Ioi]
  refine lintegral_congr_ae ?_
  have hzero : (volume : Measure ℝ) {0} = 0 := Real.volume_singleton
  have hae : ∀ᵐ z : ℝ, z ≠ 0 := by
    rw [ae_iff]
    simp [hzero]
  filter_upwards [hae] with z hz
  rcases lt_or_gt_of_ne hz with hlt | hgt
  · have hnot : z ∉ Set.Ioi (0 : ℝ) := not_lt.mpr hlt.le
    rw [Set.indicator_of_notMem hnot, hg z hlt]
  · exact Set.indicator_of_mem hgt g

lemma φ_integrable {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) :
    Integrable (D.φ k i) := by
  refine ⟨(φ_meas hD k i).aestronglyMeasurable, ?_⟩
  show ∫⁻ z, ‖D.φ k i z‖ₑ < ⊤
  have hcongr : ∀ z, ‖D.φ k i z‖ₑ = ENNReal.ofReal (D.φ k i z) := fun z =>
    Real.enorm_eq_ofReal (φ_nonneg hD k i z)
  simp_rw [hcongr, φ_lint hD k i]
  exact ENNReal.one_lt_top

lemma setIntegral_φ_eq_one {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) :
    ∫ z in Set.Ioi (0 : ℝ), D.φ k i z = 1 := by
  have hint : IntegrableOn (D.φ k i) (Set.Ioi 0) := (φ_integrable hD k i).integrableOn
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)] D.φ k i :=
    Eventually.of_forall (φ_nonneg hD k i)
  have h1 := ofReal_integral_eq_lintegral_ofReal hint hnn
  have h2 : ∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal (D.φ k i z) = 1 := by
    rw [lintegral_Ioi_eq_lintegral (fun z hz => by simp [φ_neg hD k i z hz])]
    exact φ_lint hD k i
  rw [h2] at h1
  have hnn_int : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), D.φ k i z :=
    setIntegral_nonneg measurableSet_Ioi (fun z _ => φ_nonneg hD k i z)
  have h3 := congrArg ENNReal.toReal h1
  simpa [ENNReal.toReal_ofReal hnn_int] using h3

lemma absmul_φ_eq {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) (z : ℝ) :
    |z| * D.φ k i z = z * D.φ k i z := by
  rcases lt_or_ge z 0 with hz | hz
  · rw [φ_neg hD k i z hz]; ring
  · rw [abs_of_nonneg hz]

lemma absmul_φ_integrable {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) :
    Integrable (fun z => |z| * D.φ k i z) := by
  refine ⟨(measurable_id.abs.mul (φ_meas hD k i)).aestronglyMeasurable, ?_⟩
  show ∫⁻ z, ‖|z| * D.φ k i z‖ₑ < ⊤
  have hcongr : ∀ z, ‖|z| * D.φ k i z‖ₑ = ENNReal.ofReal (z * D.φ k i z) := fun z => by
    rw [Real.enorm_eq_ofReal (mul_nonneg (abs_nonneg z) (φ_nonneg hD k i z)), absmul_φ_eq hD k i z]
  simp_rw [hcongr]
  exact lt_of_le_of_lt (φ_mean_lint hD k i) ENNReal.ofReal_lt_top

lemma setIntegral_absmul_φ_le {D : Model L} (hD : Standing D) (k : ℕ) (i : Fin L) :
    ∫ z in Set.Ioi (0 : ℝ), |z| * D.φ k i z ≤ max D.M 0 := by
  have hint : IntegrableOn (fun z => |z| * D.φ k i z) (Set.Ioi 0) :=
    (absmul_φ_integrable hD k i).integrableOn
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)] fun z => |z| * D.φ k i z :=
    Eventually.of_forall (fun z => mul_nonneg (abs_nonneg z) (φ_nonneg hD k i z))
  have h1 := ofReal_integral_eq_lintegral_ofReal hint hnn
  have h2 : ∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal (|z| * D.φ k i z) ≤ ENNReal.ofReal D.M := by
    rw [lintegral_Ioi_eq_lintegral (fun z hz => by simp [φ_neg hD k i z hz])]
    simp_rw [absmul_φ_eq hD k i]
    exact φ_mean_lint hD k i
  rw [← h1] at h2
  have hnn_int : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), |z| * D.φ k i z :=
    setIntegral_nonneg measurableSet_Ioi (fun z _ => mul_nonneg (abs_nonneg z) (φ_nonneg hD k i z))
  have h3 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
  rw [ENNReal.toReal_ofReal hnn_int] at h3
  have h4 : (ENNReal.ofReal D.M).toReal = max D.M 0 := by
    rcases le_or_gt 0 D.M with hM | hM
    · rw [ENNReal.toReal_ofReal hM, max_eq_left hM]
    · rw [ENNReal.ofReal_of_nonpos hM.le, ENNReal.toReal_zero, max_eq_right hM.le]
  linarith

lemma shift_integrable {D : Model L} (hD : Standing D) (n : ℕ) (i : Fin L)
    (b : ℝ → ℝ) (hm : Measurable b) (hnn : ∀ y, 0 ≤ b y) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hgr : ∀ y, b y ≤ Cb * (1 + |y|)) (y : ℝ) :
    Integrable (fun z => b (y - z) * D.φ n i z) := by
  refine Integrable.mono'
    (g := fun z => Cb * (1 + |y|) * D.φ n i z + Cb * (|z| * D.φ n i z))
    (((φ_integrable hD n i).const_mul _).add ((absmul_φ_integrable hD n i).const_mul _))
    ((hm.comp (measurable_const.sub measurable_id)).mul (φ_meas hD n i)).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  have hφ := φ_nonneg hD n i z
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hnn _) hφ)]
  have h1 := hgr (y - z)
  have h2 : |y - z| ≤ |y| + |z| := abs_sub y z
  calc b (y - z) * D.φ n i z ≤ Cb * (1 + |y - z|) * D.φ n i z :=
        mul_le_mul_of_nonneg_right h1 hφ
    _ ≤ Cb * (1 + (|y| + |z|)) * D.φ n i z := by gcongr
    _ = _ := by ring

lemma Fnext_nonneg {D : Model L} (hD : Standing D) (n : ℕ) (b : Fin L → ℝ → ℝ)
    (hnn : ∀ j y, 0 ≤ b j y) (i : Fin L) (y : ℝ) : 0 ≤ Fnext D n b i y := by
  unfold Fnext
  refine Finset.sum_nonneg (fun j _ => mul_nonneg (P_nonneg hD i j) ?_)
  exact setIntegral_nonneg measurableSet_Ioi (fun z _ => mul_nonneg (hnn j _) (φ_nonneg hD n i z))

lemma Fnext_growth {D : Model L} (hD : Standing D) (n : ℕ) (b : Fin L → ℝ → ℝ)
    (hm : ∀ j, Measurable (b j)) (hnn : ∀ j y, 0 ≤ b j y) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hgr : ∀ j y, b j y ≤ Cb * (1 + |y|)) (i : Fin L) (y : ℝ) :
    Fnext D n b i y ≤ Cb * (1 + max D.M 0) * (1 + |y|) := by
  unfold Fnext
  have hstep : ∀ j : Fin L,
      ∫ z in Set.Ioi (0 : ℝ), b j (y - z) * D.φ n i z ≤ Cb * (1 + max D.M 0) * (1 + |y|) := by
    intro j
    have hint1 := (shift_integrable hD n i (b j) (hm j) (hnn j) hCb (hgr j) y).integrableOn
      (s := Set.Ioi 0)
    have hint2 : IntegrableOn (fun z => Cb * (1 + |y|) * D.φ n i z + Cb * (|z| * D.φ n i z))
        (Set.Ioi 0) :=
      (((φ_integrable hD n i).const_mul _).add
        ((absmul_φ_integrable hD n i).const_mul _)).integrableOn
    have hle : ∫ z in Set.Ioi (0 : ℝ), b j (y - z) * D.φ n i z ≤
        ∫ z in Set.Ioi (0 : ℝ), (Cb * (1 + |y|) * D.φ n i z + Cb * (|z| * D.φ n i z)) := by
      refine setIntegral_mono_on hint1 hint2 measurableSet_Ioi (fun z _ => ?_)
      have hφ := φ_nonneg hD n i z
      have h1 := hgr j (y - z)
      have h2 : |y - z| ≤ |y| + |z| := abs_sub y z
      calc b j (y - z) * D.φ n i z ≤ Cb * (1 + |y - z|) * D.φ n i z :=
            mul_le_mul_of_nonneg_right h1 hφ
        _ ≤ Cb * (1 + (|y| + |z|)) * D.φ n i z := by gcongr
        _ = _ := by ring
    rw [integral_add ((φ_integrable hD n i).const_mul _).integrableOn
          ((absmul_φ_integrable hD n i).const_mul _).integrableOn,
        integral_const_mul, integral_const_mul, setIntegral_φ_eq_one hD n i] at hle
    have hM := setIntegral_absmul_φ_le hD n i
    have hM0 : 0 ≤ max D.M 0 := le_max_right _ _
    have habs : 0 ≤ |y| := abs_nonneg y
    have h3 : 0 ≤ Cb * max D.M 0 * |y| := by positivity
    have h4 : Cb * ∫ z in Set.Ioi (0 : ℝ), |z| * D.φ n i z ≤ Cb * max D.M 0 :=
      mul_le_mul_of_nonneg_left hM hCb
    linarith
  calc ∑ j, D.P i j * ∫ z in Set.Ioi (0 : ℝ), b j (y - z) * D.φ n i z
      ≤ ∑ j, D.P i j * (Cb * (1 + max D.M 0) * (1 + |y|)) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hstep j) (P_nonneg hD i j))
    _ = (∑ j, D.P i j) * (Cb * (1 + max D.M 0) * (1 + |y|)) := (Finset.sum_mul ..).symm
    _ = _ := by rw [P_sum hD i, one_mul]

lemma Fnext_mono {D : Model L} (hD : Standing D) (n : ℕ) (b₁ b₂ : Fin L → ℝ → ℝ)
    (hm₁ : ∀ j, Measurable (b₁ j)) (hnn₁ : ∀ j y, 0 ≤ b₁ j y)
    (hgr₁ : ∃ Cb, 0 ≤ Cb ∧ ∀ j y, b₁ j y ≤ Cb * (1 + |y|))
    (hm₂ : ∀ j, Measurable (b₂ j)) (hnn₂ : ∀ j y, 0 ≤ b₂ j y)
    (hgr₂ : ∃ Cb, 0 ≤ Cb ∧ ∀ j y, b₂ j y ≤ Cb * (1 + |y|))
    (hle : ∀ j y, b₁ j y ≤ b₂ j y) (i : Fin L) (y : ℝ) :
    Fnext D n b₁ i y ≤ Fnext D n b₂ i y := by
  obtain ⟨C₁, hC₁, hg₁⟩ := hgr₁
  obtain ⟨C₂, hC₂, hg₂⟩ := hgr₂
  unfold Fnext
  refine Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left ?_ (P_nonneg hD i j))
  refine setIntegral_mono_on
    (shift_integrable hD n i (b₁ j) (hm₁ j) (hnn₁ j) hC₁ (hg₁ j) y).integrableOn
    (shift_integrable hD n i (b₂ j) (hm₂ j) (hnn₂ j) hC₂ (hg₂ j) y).integrableOn
    measurableSet_Ioi (fun z _ => mul_le_mul_of_nonneg_right (hle j _) (φ_nonneg hD n i z))

lemma Fnext_lipschitz {D : Model L} (hD : Standing D) (n : ℕ) (b : Fin L → ℝ → ℝ)
    (hm : ∀ j, Measurable (b j)) (hnn : ∀ j y, 0 ≤ b j y)
    (hgr : ∃ Cb, 0 ≤ Cb ∧ ∀ j y, b j y ≤ Cb * (1 + |y|))
    {K : ℝ} (_hK : 0 ≤ K) (hlip : ∀ j y y', |b j y' - b j y| ≤ K * |y' - y|)
    (i : Fin L) (y y' : ℝ) :
    |Fnext D n b i y' - Fnext D n b i y| ≤ K * |y' - y| := by
  obtain ⟨Cb, hCb, hg⟩ := hgr
  unfold Fnext
  rw [← Finset.sum_sub_distrib]
  have hstep : ∀ j : Fin L,
      |D.P i j * (∫ z in Set.Ioi (0 : ℝ), b j (y' - z) * D.φ n i z) -
       D.P i j * (∫ z in Set.Ioi (0 : ℝ), b j (y - z) * D.φ n i z)| ≤
      D.P i j * (K * |y' - y|) := by
    intro j
    rw [← mul_sub, abs_mul, abs_of_nonneg (P_nonneg hD i j)]
    refine mul_le_mul_of_nonneg_left ?_ (P_nonneg hD i j)
    have h1 := (shift_integrable hD n i (b j) (hm j) (hnn j) hCb (hg j) y').integrableOn
      (s := Set.Ioi 0)
    have h2 := (shift_integrable hD n i (b j) (hm j) (hnn j) hCb (hg j) y).integrableOn
      (s := Set.Ioi 0)
    rw [← integral_sub h1 h2]
    calc |∫ z in Set.Ioi (0 : ℝ), (b j (y' - z) * D.φ n i z - b j (y - z) * D.φ n i z)|
        ≤ ∫ z in Set.Ioi (0 : ℝ), |b j (y' - z) * D.φ n i z - b j (y - z) * D.φ n i z| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ z in Set.Ioi (0 : ℝ), (K * |y' - y|) * D.φ n i z := by
          refine setIntegral_mono_on (h1.sub h2).abs ((φ_integrable hD n i).const_mul _).integrableOn
            measurableSet_Ioi (fun z _ => ?_)
          rw [← sub_mul, abs_mul, abs_of_nonneg (φ_nonneg hD n i z)]
          have heq : (y' - z) - (y - z) = y' - y := by ring
          have := hlip j (y - z) (y' - z)
          rw [heq] at this
          exact mul_le_mul_of_nonneg_right this (φ_nonneg hD n i z)
      _ = K * |y' - y| := by
          rw [integral_const_mul, setIntegral_φ_eq_one hD n i, mul_one]
  calc |∑ j, (D.P i j * (∫ z in Set.Ioi (0 : ℝ), b j (y' - z) * D.φ n i z) -
          D.P i j * (∫ z in Set.Ioi (0 : ℝ), b j (y - z) * D.φ n i z))|
      ≤ ∑ j, |D.P i j * (∫ z in Set.Ioi (0 : ℝ), b j (y' - z) * D.φ n i z) -
          D.P i j * (∫ z in Set.Ioi (0 : ℝ), b j (y - z) * D.φ n i z)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, D.P i j * (K * |y' - y|) := Finset.sum_le_sum (fun j _ => hstep j)
    _ = (∑ j, D.P i j) * (K * |y' - y|) := (Finset.sum_mul ..).symm
    _ = K * |y' - y| := by rw [P_sum hD i, one_mul]

lemma ofReal_Fnext {D : Model L} (hD : Standing D) (n : ℕ) (b : Fin L → ℝ → ℝ)
    (hm : ∀ j, Measurable (b j)) (hnn : ∀ j y, 0 ≤ b j y)
    (hgr : ∃ Cb, 0 ≤ Cb ∧ ∀ j y, b j y ≤ Cb * (1 + |y|)) (i : Fin L) (y : ℝ) :
    ENNReal.ofReal (Fnext D n b i y) =
      ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
        ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) * ENNReal.ofReal (b j (y - z)) := by
  obtain ⟨Cb, hCb, hg⟩ := hgr
  unfold Fnext
  rw [ENNReal.ofReal_sum_of_nonneg]
  swap
  · intro j _
    exact mul_nonneg (P_nonneg hD i j)
      (setIntegral_nonneg measurableSet_Ioi (fun z _ => mul_nonneg (hnn j _) (φ_nonneg hD n i z)))
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [ENNReal.ofReal_mul (P_nonneg hD i j)]
  congr 1
  have hint := (shift_integrable hD n i (b j) (hm j) (hnn j) hCb (hg j) y).integrableOn
    (s := Set.Ioi 0)
  have hae : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)] fun z => b j (y - z) * D.φ n i z :=
    Eventually.of_forall (fun z => mul_nonneg (hnn j _) (φ_nonneg hD n i z))
  rw [ofReal_integral_eq_lintegral_ofReal hint hae]
  rw [lintegral_Ioi_eq_lintegral (fun z hz => by simp [φ_neg hD n i z hz])]
  refine lintegral_congr (fun z => ?_)
  rw [mul_comm, ENNReal.ofReal_mul (φ_nonneg hD n i z)]

/-! ### Section 2: Regularity of `dpTrunc` -/

lemma lipschitz_uniformContinuous {g : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hlip : ∀ x x', |g x' - g x| ≤ K * |x' - x|) : UniformContinuous g := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  refine ⟨ε / (K + 1), div_pos hε (by linarith), fun {x y} hxy => ?_⟩
  rw [Real.dist_eq] at hxy ⊢
  calc |g x - g y| ≤ K * |x - y| := hlip y x
    _ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hxy.le hK
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith : (0 : ℝ) < K + 1)]
      nlinarith

lemma lipschitz_continuous {g : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hlip : ∀ x x', |g x' - g x| ≤ K * |x' - x|) : Continuous g :=
  (lipschitz_uniformContinuous hK hlip).continuous

lemma dpTrunc_props {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ k n,
      (∀ i x, 0 ≤ dpTrunc D α n k i x) ∧
      (∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ i x, dpTrunc D α n k i x ≤ Cb * (1 + |x|)) ∧
      (∀ i x x', |dpTrunc D α n k i x' - dpTrunc D α n k i x| ≤
        (D.C / (1 - α)) * |x' - x|) := by
  intro k
  have hC := C_pos hD
  have h1α : 0 < 1 - α := by linarith
  have hLipNN : 0 ≤ D.C / (1 - α) := div_nonneg hC.le h1α.le
  induction k with
  | zero =>
    intro n
    refine ⟨fun _ _ => le_rfl, ⟨0, le_rfl, fun _ _ => by simp [dpTrunc]⟩, fun _ _ _ => ?_⟩
    simp only [dpTrunc, sub_self, abs_zero]
    exact mul_nonneg hLipNN (abs_nonneg _)
  | succ k ih =>
    intro n
    obtain ⟨hnn_k, ⟨Cb_k, hCb_k, hgr_k⟩, hlip_k⟩ := ih (n + 1)
    have hm_k : ∀ j, Measurable (dpTrunc D α (n + 1) k j) := fun j =>
      (lipschitz_continuous hLipNN (hlip_k j)).measurable
    set g : Fin L → ℝ → ℝ := fun i y => α * Fnext D n (dpTrunc D α (n + 1) k) i y
    have hg_nn : ∀ i y, 0 ≤ g i y := fun i y =>
      mul_nonneg hα0.le (Fnext_nonneg hD n _ hnn_k i y)
    have hg_gr : ∀ i y, g i y ≤ (α * (Cb_k * (1 + max D.M 0))) * (1 + |y|) := fun i y => by
      have := Fnext_growth hD n _ hm_k hnn_k hCb_k hgr_k i y
      have : α * Fnext D n (dpTrunc D α (n + 1) k) i y ≤
          α * (Cb_k * (1 + max D.M 0) * (1 + |y|)) :=
        mul_le_mul_of_nonneg_left this hα0.le
      linarith
    have hg_lip : ∀ i y y', |g i y' - g i y| ≤ (α * (D.C / (1 - α))) * |y' - y| := fun i y y' => by
      show |α * Fnext D n _ i y' - α * Fnext D n _ i y| ≤ _
      rw [← mul_sub, abs_mul, abs_of_pos hα0]
      have := Fnext_lipschitz hD n _ hm_k hnn_k ⟨Cb_k, hCb_k, hgr_k⟩ hLipNN hlip_k i y y'
      calc α * |Fnext D n _ i y' - Fnext D n _ i y| ≤ α * ((D.C / (1 - α)) * |y' - y|) :=
            mul_le_mul_of_nonneg_left this hα0.le
        _ = _ := by ring
    have hbdd : ∀ i x, BddBelow (Set.range (fun u : {u : ℝ // 0 ≤ u} =>
        orderCost D n i u + g i (x + u))) := fun i x =>
      ⟨0, by rintro _ ⟨u, rfl⟩; exact add_nonneg (orderCost_nonneg hD u.2) (hg_nn i _)⟩
    set H : Fin L → ℝ → ℝ := fun i x =>
      ⨅ u : {u : ℝ // 0 ≤ u}, (orderCost D n i u + g i (x + u))
    have hH_nn : ∀ i x, 0 ≤ H i x := fun i x =>
      le_ciInf (fun u => add_nonneg (orderCost_nonneg hD u.2) (hg_nn i _))
    have hH_le_g : ∀ i x, H i x ≤ g i x := fun i x => by
      have := ciInf_le (hbdd i x) (⟨0, le_rfl⟩ : {u : ℝ // 0 ≤ u})
      simpa [orderCost_zero] using this
    have hH_lip_sub : ∀ i x x', H i x' - H i x ≤ (α * (D.C / (1 - α))) * |x' - x| := by
      intro i x x'
      have hle : H i x' ≤ H i x + (α * (D.C / (1 - α))) * |x' - x| := by
        have : H i x' - (α * (D.C / (1 - α))) * |x' - x| ≤ H i x := by
          refine le_ciInf (fun u => ?_)
          have h1 : H i x' ≤ orderCost D n i u + g i (x' + u) := ciInf_le (hbdd i x') u
          have h2 := (abs_le.mp (hg_lip i (x + u) (x' + u))).2
          have heq : (x' + u.1) - (x + u.1) = x' - x := by ring
          rw [heq] at h2
          linarith
        linarith
      linarith
    have hH_lip : ∀ i x x', |H i x' - H i x| ≤ (α * (D.C / (1 - α))) * |x' - x| := by
      intro i x x'
      rw [abs_le]
      exact ⟨by have := hH_lip_sub i x' x; rw [abs_sub_comm] at this; linarith,
             hH_lip_sub i x x'⟩
    have hdp_eq : ∀ i x, dpTrunc D α n (k + 1) i x = D.f n i x + H i x := fun _ _ => rfl
    refine ⟨fun i x => by rw [hdp_eq]; exact add_nonneg (f_nonneg hD n i x) (hH_nn i x),
            ⟨D.C + α * (Cb_k * (1 + max D.M 0)), by positivity, fun i x => ?_⟩,
            fun i x x' => ?_⟩
    · rw [hdp_eq]
      have h1 := f_growth hD n i x
      have h2 := (hH_le_g i x).trans (hg_gr i x)
      linarith
    · rw [hdp_eq, hdp_eq]
      have h1 := f_lipschitz hD n i x x'
      have h2 := hH_lip i x x'
      have htri : |D.f n i x' + H i x' - (D.f n i x + H i x)| ≤
          |D.f n i x' - D.f n i x| + |H i x' - H i x| := by
        have : D.f n i x' + H i x' - (D.f n i x + H i x) =
            (D.f n i x' - D.f n i x) + (H i x' - H i x) := by ring
        rw [this]
        exact abs_add_le _ _
      have hconst : D.C + α * (D.C / (1 - α)) = D.C / (1 - α) := by
        have hne : 1 - α ≠ 0 := h1α.ne'
        field_simp
        ring
      calc |D.f n i x' + H i x' - (D.f n i x + H i x)|
          ≤ D.C * |x' - x| + (α * (D.C / (1 - α))) * |x' - x| := by linarith
        _ = (D.C + α * (D.C / (1 - α))) * |x' - x| := by ring
        _ = (D.C / (1 - α)) * |x' - x| := by rw [hconst]

lemma dpTrunc_nonneg {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n k : ℕ) (i : Fin L) (x : ℝ) : 0 ≤ dpTrunc D α n k i x :=
  (dpTrunc_props hD hα0 hα1 k n).1 i x

lemma dpTrunc_growth {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n k : ℕ) : ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ i x, dpTrunc D α n k i x ≤ Cb * (1 + |x|) :=
  (dpTrunc_props hD hα0 hα1 k n).2.1

lemma dpTrunc_lipschitz {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n k : ℕ) (i : Fin L) (x x' : ℝ) :
    |dpTrunc D α n k i x' - dpTrunc D α n k i x| ≤ (D.C / (1 - α)) * |x' - x| :=
  (dpTrunc_props hD hα0 hα1 k n).2.2 i x x'

lemma dpTrunc_continuous {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n k : ℕ) (i : Fin L) : Continuous (dpTrunc D α n k i) :=
  lipschitz_continuous (div_nonneg (C_pos hD).le (by linarith)) (dpTrunc_lipschitz hD hα0 hα1 n k i)

lemma dpTrunc_measurable {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n k : ℕ) (i : Fin L) : Measurable (dpTrunc D α n k i) :=
  (dpTrunc_continuous hD hα0 hα1 n k i).measurable

lemma dpTrunc_ge_f {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n k : ℕ) (i : Fin L) (x : ℝ) : D.f n i x ≤ dpTrunc D α n (k + 1) i x := by
  show D.f n i x ≤ D.f n i x + ⨅ u : {u : ℝ // 0 ≤ u},
    (orderCost D n i u + α * Fnext D n (dpTrunc D α (n + 1) k) i (x + u))
  have hnn : 0 ≤ ⨅ u : {u : ℝ // 0 ≤ u},
      (orderCost D n i u + α * Fnext D n (dpTrunc D α (n + 1) k) i (x + u)) :=
    le_ciInf (fun u => add_nonneg (orderCost_nonneg hD u.2)
      (mul_nonneg hα0.le (Fnext_nonneg hD n _ (dpTrunc_nonneg hD hα0 hα1 (n + 1) k) i _)))
  linarith

/-! ### Section 3: One-step `Jtrunc` identity via `Fin.cons` and feedback policies -/

lemma meas_init {m : ℕ} : Measurable (fun ξ : Fin (m + 1) → ℝ => Fin.init ξ) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

lemma meas_dmHist {m : ℕ} (t : Fin m) : Measurable (fun ξ : Fin m → ℝ => dmHist ξ t) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

lemma meas_surplus (U : Policy L) (x : ℝ) (hU : ∀ k σ, Measurable (U k σ)) :
    ∀ k, ∀ σ : Fin (k + 1) → Fin L, Measurable (surplus U x k σ) := by
  intro k
  induction k with
  | zero => intro σ; exact measurable_const
  | succ k ih =>
    intro σ
    exact (((ih _).comp meas_init).add ((hU k _).comp meas_init)).sub (measurable_pi_apply _)

lemma meas_delta : Measurable delta := by
  unfold delta
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
    measurable_const

lemma meas_orderCost (D : Model L) (k : ℕ) (j : Fin L) : Measurable (orderCost D k j) := by
  unfold orderCost
  exact (measurable_const.mul meas_delta).add (measurable_const.mul measurable_id)

lemma meas_truncCost {D : Model L} (hD : Standing D) (α : ℝ) (n : ℕ) (U : Policy L) (x : ℝ)
    (hU : ∀ k σ, Measurable (U k σ)) {k : ℕ} (σ : Fin (k + 1) → Fin L) :
    Measurable (fun ξ => truncCost D α n U x σ ξ) := by
  unfold truncCost
  refine Finset.measurable_sum _ (fun t _ => ?_)
  exact measurable_const.mul (((meas_orderCost D _ _).comp ((hU _ _).comp (meas_dmHist t))).add
    ((f_continuous hD _ _).measurable.comp ((meas_surplus U x hU _ _).comp (meas_dmHist t))))

lemma meas_pathWeight {D : Model L} (hD : Standing D) (n : ℕ) {t : ℕ}
    (σ : Fin (t + 1) → Fin L) : Measurable (fun ξ : Fin t → ℝ => pathWeight D n σ ξ) := by
  unfold pathWeight
  exact Finset.measurable_prod _ (fun k _ =>
    measurable_const.mul ((φ_meas hD _ _).comp (measurable_pi_apply _)))

lemma pathWeight_nonneg {D : Model L} (hD : Standing D) (n : ℕ) {t : ℕ}
    (σ : Fin (t + 1) → Fin L) (ξ : Fin t → ℝ) : 0 ≤ pathWeight D n σ ξ := by
  unfold pathWeight
  exact Finset.prod_nonneg (fun k _ => mul_nonneg (P_nonneg hD _ _) (φ_nonneg hD _ _ _))

lemma truncCost_nonneg {D : Model L} (hD : Standing D) {α : ℝ} (hα : 0 ≤ α) (n : ℕ)
    (U : Policy L) (hU : ∀ t σ ξ, 0 ≤ U t σ ξ) (x : ℝ) {k : ℕ}
    (σ : Fin (k + 1) → Fin L) (ξ : Fin k → ℝ) : 0 ≤ truncCost D α n U x σ ξ := by
  unfold truncCost
  exact Finset.sum_nonneg (fun t _ => mul_nonneg (pow_nonneg hα _)
    (add_nonneg (orderCost_nonneg hD (hU _ _ _)) (f_nonneg hD _ _ _)))

lemma sum_cons_ite {k : ℕ} (i : Fin L) (F : (Fin (k + 2) → Fin L) → ℝ≥0∞) :
    (∑ σ : Fin (k + 2) → Fin L, if σ 0 = i then F σ else 0) =
      ∑ σ' : Fin (k + 1) → Fin L, F (Fin.cons i σ') := by
  rw [← (Fin.consEquiv (fun _ : Fin (k + 2) => Fin L)).sum_comp, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · simp [Fin.consEquiv]
  · intro j _ hji
    simp [Fin.consEquiv, hji]
  · intro hi; exact absurd (Finset.mem_univ i) hi

lemma sum_group_head {k : ℕ} (F : (Fin (k + 1) → Fin L) → ℝ≥0∞) :
    ∑ σ' : Fin (k + 1) → Fin L, F σ' =
      ∑ j : Fin L, ∑ σ' : Fin (k + 1) → Fin L, if σ' 0 = j then F σ' else 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun σ' _ => ?_)
  simp

lemma cons_symm_eq (t : ℕ) (p : ℝ × (Fin t → ℝ)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) => ℝ) 0).symm p =
      (Fin.cons p.1 p.2 : Fin (t + 1) → ℝ) := by
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
  rfl

lemma lintegral_cons (t : ℕ) (G : (Fin (t + 1) → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ ξ' : Fin (t + 1) → ℝ, G ξ' ∂(Measure.pi fun _ => volume) =
      ∫⁻ z : ℝ, ∫⁻ ξ : Fin t → ℝ, G (Fin.cons z ξ : Fin (t + 1) → ℝ)
        ∂(Measure.pi fun _ => volume) := by
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (t + 1) => ℝ) 0
  have hvol1 : (Measure.pi fun _ : Fin (t + 1) => (volume : Measure ℝ)) = volume := rfl
  have hvol2 : (Measure.pi fun _ : Fin t => (volume : Measure ℝ)) = volume := rfl
  rw [hvol1, hvol2]
  have h1 : ∫⁻ p, G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) => ℝ) 0).symm p)
      ∂((volume : Measure ℝ).prod (Measure.pi fun _ : Fin t => (volume : Measure ℝ))) =
      ∫⁻ ξ', G ξ' := (MeasurePreserving.symm _ hmp).lintegral_comp hG
  have h2 : ∫⁻ p, G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) => ℝ) 0).symm p)
      ∂((volume : Measure ℝ).prod (Measure.pi fun _ : Fin t => (volume : Measure ℝ))) =
      ∫⁻ z, ∫⁻ ξ, G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) => ℝ) 0).symm (z, ξ))
        ∂(Measure.pi fun _ : Fin t => (volume : Measure ℝ)) ∂(volume : Measure ℝ) :=
    lintegral_prod _ (hG.comp (MeasurableEquiv.measurable _)).aemeasurable
  rw [← h1, h2]
  simp only [cons_symm_eq]
  rfl

lemma init_cons_zero {β : Type*} (a : β) (v : Fin 1 → β) :
    Fin.init (Fin.cons a v : Fin 2 → β) = fun _ => a := by
  funext j; fin_cases j; rfl

lemma init_cons {β : Type*} {t : ℕ} (a : β) (v : Fin (t + 1) → β) :
    Fin.init (Fin.cons a v : Fin (t + 2) → β) = Fin.cons a (Fin.init v) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · rfl
  · intro k; rfl

lemma cons_last_succ {β : Type*} {t : ℕ} (a : β) (v : Fin (t + 1) → β) :
    (Fin.cons a v : Fin (t + 2) → β) (Fin.last (t + 1)) = v (Fin.last t) := by
  rw [← Fin.succ_last, Fin.cons_succ]

lemma stHist_cons_zero {k : ℕ} (i : Fin L) (σ' : Fin (k + 1) → Fin L) :
    stHist (Fin.cons i σ' : Fin (k + 2) → Fin L) 0 = fun _ => i := by
  funext j; fin_cases j; rfl

lemma dmHist_cons_zero {k : ℕ} (z : ℝ) (ξ' : Fin k → ℝ) :
    dmHist (Fin.cons z ξ' : Fin (k + 1) → ℝ) 0 = Fin.elim0 := by
  funext j; exact Fin.elim0 j

lemma stHist_cons_succ {k : ℕ} (i : Fin L) (σ' : Fin (k + 1) → Fin L) (t : Fin k) :
    stHist (Fin.cons i σ' : Fin (k + 2) → Fin L) t.succ = Fin.cons i (stHist σ' t) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · rfl
  · intro a
    simp only [stHist, Fin.cons_succ]
    have hcast : Fin.castLE (Nat.succ_le_succ t.succ.isLt.le) a.succ =
        (Fin.castLE (Nat.succ_le_succ t.isLt.le) a).succ := by
      ext; simp
    rw [hcast, Fin.cons_succ]

lemma dmHist_cons_succ {k : ℕ} (z : ℝ) (ξ' : Fin k → ℝ) (t : Fin k) :
    dmHist (Fin.cons z ξ' : Fin (k + 1) → ℝ) t.succ = Fin.cons z (dmHist ξ' t) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · rfl
  · intro a
    simp only [dmHist, Fin.cons_succ]
    have hcast : Fin.castLE t.succ.isLt.le a.succ = (Fin.castLE t.isLt.le a).succ := by
      ext; simp
    rw [hcast, Fin.cons_succ]

/-- The shifted policy after observing initial state `i` and first demand `z`. -/
def shiftPolicy (U : Policy L) (i : Fin L) (z : ℝ) : Policy L :=
  fun t σ' ξ' => U (t + 1) (Fin.cons i σ') (Fin.cons z ξ')

lemma meas_cons_const {t : ℕ} (z : ℝ) :
    Measurable (fun ξ' : Fin t → ℝ => (Fin.cons z ξ' : Fin (t + 1) → ℝ)) :=
  measurable_pi_lambda _ (fun j => Fin.cases measurable_const (fun k => measurable_pi_apply k) j)

lemma shiftPolicy_admissible {U : Policy L} (hU : Admissible U) (i : Fin L) (z : ℝ) :
    Admissible (shiftPolicy U i z) :=
  ⟨fun t σ' ξ' => hU.1 (t + 1) (Fin.cons i σ') (Fin.cons z ξ'),
   fun t σ' => (hU.2 (t + 1) (Fin.cons i σ')).comp (meas_cons_const z)⟩

lemma surplus_cons (U : Policy L) (x : ℝ) (i : Fin L) (z : ℝ) :
    ∀ t (σ' : Fin (t + 1) → Fin L) (ξ' : Fin t → ℝ),
      surplus U x (t + 1) (Fin.cons i σ') (Fin.cons z ξ') =
        surplus (shiftPolicy U i z) (x + U 0 (fun _ => i) Fin.elim0 - z) t σ' ξ' := by
  intro t
  induction t with
  | zero =>
    intro σ' ξ'
    simp only [surplus, init_cons_zero]
    have hξ : Fin.init (Fin.cons z ξ' : Fin 1 → ℝ) = Fin.elim0 := by
      funext j; exact Fin.elim0 j
    have hlast : (Fin.cons z ξ' : Fin 1 → ℝ) (Fin.last 0) = z := rfl
    rw [hξ, hlast]
  | succ t ih =>
    intro σ' ξ'
    conv_lhs => rw [surplus]
    conv_rhs => rw [surplus]
    rw [init_cons, init_cons, cons_last_succ, ih (Fin.init σ') (Fin.init ξ')]
    rfl

lemma pathWeight_cons (D : Model L) (n : ℕ) {k : ℕ} (i : Fin L) (σ' : Fin (k + 1) → Fin L)
    (z : ℝ) (ξ' : Fin k → ℝ) :
    pathWeight D n (Fin.cons i σ' : Fin (k + 2) → Fin L) (Fin.cons z ξ' : Fin (k + 1) → ℝ) =
      (D.P i (σ' 0) * D.φ n i z) * pathWeight D (n + 1) σ' ξ' := by
  unfold pathWeight
  rw [Fin.prod_univ_succ]
  congr 1
  refine Finset.prod_congr rfl (fun t _ => ?_)
  have h1 : (Fin.cons i σ' : Fin (k + 2) → Fin L) t.succ.castSucc = σ' t.castSucc := by
    have : t.succ.castSucc = t.castSucc.succ := by ext; simp
    rw [this, Fin.cons_succ]
  have h2 : (Fin.cons i σ' : Fin (k + 2) → Fin L) t.succ.succ = σ' t.succ := Fin.cons_succ ..
  have h3 : (Fin.cons z ξ' : Fin (k + 1) → ℝ) t.succ = ξ' t := Fin.cons_succ ..
  have h4 : n + (t.succ : ℕ) = (n + 1) + (t : ℕ) := by simp; omega
  rw [h1, h2, h3, h4]

lemma truncCost_cons (D : Model L) (α : ℝ) (n : ℕ) (U : Policy L) (x : ℝ) {k : ℕ}
    (i : Fin L) (σ' : Fin (k + 1) → Fin L) (z : ℝ) (ξ' : Fin k → ℝ) :
    truncCost D α n U x (Fin.cons i σ' : Fin (k + 2) → Fin L) (Fin.cons z ξ' : Fin (k + 1) → ℝ) =
      (D.f n i x + orderCost D n i (U 0 (fun _ => i) Fin.elim0)) +
        α * truncCost D α (n + 1) (shiftPolicy U i z)
          (x + U 0 (fun _ => i) Fin.elim0 - z) σ' ξ' := by
  unfold truncCost
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  congr 1
  · simp only [Fin.val_zero, pow_zero, one_mul, add_zero, Fin.castSucc_zero, Fin.cons_zero,
      stHist_cons_zero, dmHist_cons_zero, surplus]
    ring
  · refine Finset.sum_congr rfl (fun t _ => ?_)
    have h1 : (Fin.cons i σ' : Fin (k + 2) → Fin L) t.succ.castSucc = σ' t.castSucc := by
      have : t.succ.castSucc = t.castSucc.succ := by ext; simp
      rw [this, Fin.cons_succ]
    have h2 : n + (t.succ : ℕ) = (n + 1) + (t : ℕ) := by simp; omega
    have h3 : α ^ (t.succ : ℕ) = α * α ^ (t : ℕ) := by simp [pow_succ']
    rw [h1, h2, h3, mul_assoc]
    congr 2
    rw [stHist_cons_succ, dmHist_cons_succ]
    change orderCost D (n + 1 + ↑t) (σ' t.castSucc)
        (shiftPolicy U i z (↑t) (stHist σ' t) (dmHist ξ' t)) +
      D.f (n + 1 + ↑t) (σ' t.castSucc)
        (surplus U x ((t : ℕ) + 1) (Fin.cons i (stHist σ' t)) (Fin.cons z (dmHist ξ' t))) = _
    rw [surplus_cons]

lemma weight_sum {D : Model L} (hD : Standing D) :
    ∀ k n (i : Fin L),
      (∑ σ : Fin (k + 1) → Fin L, if σ 0 = i then
        ∫⁻ ξ : Fin k → ℝ, ENNReal.ofReal (pathWeight D n σ ξ) ∂(Measure.pi fun _ => volume)
        else 0) = 1 := by
  intro k
  induction k with
  | zero =>
    intro n i
    rw [Fintype.sum_eq_single (fun _ => i)]
    · unfold pathWeight; simp
    · intro σ hσ
      rw [if_neg]
      intro h
      apply hσ
      funext a; fin_cases a; exact h
  | succ k ih =>
    intro n i
    rw [sum_cons_ite]
    have hterm : ∀ σ' : Fin (k + 1) → Fin L,
        ∫⁻ ξ : Fin (k + 1) → ℝ, ENNReal.ofReal (pathWeight D n (Fin.cons i σ') ξ)
          ∂(Measure.pi fun _ => volume) =
        ENNReal.ofReal (D.P i (σ' 0)) *
          ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')
            ∂(Measure.pi fun _ => volume) := by
      intro σ'
      have hpw_m' : Measurable (fun ξ : Fin (k + 1) → ℝ =>
          ENNReal.ofReal (pathWeight D n (Fin.cons i σ') ξ)) :=
        ENNReal.measurable_ofReal.comp (meas_pathWeight hD n _)
      rw [lintegral_cons k _ hpw_m']
      have hinner : ∀ z : ℝ,
          ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D n (Fin.cons i σ') (Fin.cons z ξ'))
            ∂(Measure.pi fun _ => volume) =
          (ENNReal.ofReal (D.P i (σ' 0)) * ENNReal.ofReal (D.φ n i z)) *
            ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')
              ∂(Measure.pi fun _ => volume) := by
        intro z
        have heq : ∀ ξ', ENNReal.ofReal (pathWeight D n (Fin.cons i σ') (Fin.cons z ξ')) =
            (ENNReal.ofReal (D.P i (σ' 0)) * ENNReal.ofReal (D.φ n i z)) *
              ENNReal.ofReal (pathWeight D (n + 1) σ' ξ') := by
          intro ξ'
          rw [pathWeight_cons, ENNReal.ofReal_mul (mul_nonneg (P_nonneg hD _ _) (φ_nonneg hD _ _ _)),
              ENNReal.ofReal_mul (P_nonneg hD _ _)]
        simp_rw [heq]
        exact lintegral_const_mul _ (ENNReal.measurable_ofReal.comp (meas_pathWeight hD (n + 1) σ'))
      simp_rw [hinner]
      have mφ : Measurable (fun z : ℝ => ENNReal.ofReal (D.φ n i z)) :=
        ENNReal.measurable_ofReal.comp (φ_meas hD n i)
      calc ∫⁻ z : ℝ, (ENNReal.ofReal (D.P i (σ' 0)) * ENNReal.ofReal (D.φ n i z)) *
              ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')
                ∂(Measure.pi fun _ => volume)
          = (ENNReal.ofReal (D.P i (σ' 0)) *
              ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')
                ∂(Measure.pi fun _ => volume)) * ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) := by
            rw [← lintegral_const_mul _ mφ]
            refine lintegral_congr (fun z => by ring)
        _ = _ := by rw [φ_lint hD n i, mul_one]
    simp_rw [hterm]
    rw [sum_group_head]
    have hgroup : ∀ j : Fin L,
        (∑ σ' : Fin (k + 1) → Fin L, if σ' 0 = j then
          ENNReal.ofReal (D.P i (σ' 0)) *
            ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')
              ∂(Measure.pi fun _ => volume) else 0) =
        ENNReal.ofReal (D.P i j) := by
      intro j
      have : (∑ σ' : Fin (k + 1) → Fin L, if σ' 0 = j then
          ENNReal.ofReal (D.P i (σ' 0)) *
            ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')
              ∂(Measure.pi fun _ => volume) else 0) =
          ENNReal.ofReal (D.P i j) *
            ∑ σ' : Fin (k + 1) → Fin L, if σ' 0 = j then
              ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')
                ∂(Measure.pi fun _ => volume) else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun σ' _ => ?_)
        split_ifs with h
        · rw [h]
        · simp
      rw [this, ih (n + 1) j, mul_one]
    simp_rw [hgroup]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => P_nonneg hD i j), P_sum hD i, ENNReal.ofReal_one]

/-- Master one-step Bellman decomposition for `Jtrunc` of any admissible policy. -/
theorem Jtrunc_cons {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α)
    (n k : ℕ) (i : Fin L) (x : ℝ) (U : Policy L) (hU : Admissible U) :
    Jtrunc D α n (k + 1) i x U =
      ENNReal.ofReal (D.f n i x + orderCost D n i (U 0 (fun _ => i) Fin.elim0)) +
      ENNReal.ofReal α * ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
        ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) *
          Jtrunc D α (n + 1) k j (x + U 0 (fun _ => i) Fin.elim0 - z) (shiftPolicy U i z) := by
  set u₀ := U 0 (fun _ => i) Fin.elim0
  set c₀ := D.f n i x + orderCost D n i u₀
  have hc₀_nn : 0 ≤ c₀ := add_nonneg (f_nonneg hD n i x) (orderCost_nonneg hD (hU.1 0 _ _))
  unfold Jtrunc
  rw [sum_cons_ite]
  -- Rewrite each `σ'` summand as a sum of immediate-cost part and discounted continuation part
  have hsplit : ∀ σ' : Fin (k + 1) → Fin L,
      ∫⁻ ξ : Fin (k + 1) → ℝ, ENNReal.ofReal (pathWeight D n (Fin.cons i σ') ξ) *
          ENNReal.ofReal (truncCost D α n U x (Fin.cons i σ') ξ)
          ∂(Measure.pi fun _ => volume) =
      (ENNReal.ofReal c₀ * ENNReal.ofReal (D.P i (σ' 0)) *
        ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')
          ∂(Measure.pi fun _ => volume)) +
      (ENNReal.ofReal α * ENNReal.ofReal (D.P i (σ' 0)) *
        ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) *
          ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ') *
            ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i z) (x + u₀ - z) σ' ξ')
            ∂(Measure.pi fun _ => volume)) := by
    intro σ'
    have hGm : Measurable (fun ξ : Fin (k + 1) → ℝ =>
        ENNReal.ofReal (pathWeight D n (Fin.cons i σ') ξ) *
          ENNReal.ofReal (truncCost D α n U x (Fin.cons i σ') ξ)) :=
      (ENNReal.measurable_ofReal.comp (meas_pathWeight hD n _)).mul
        (ENNReal.measurable_ofReal.comp (meas_truncCost hD α n U x hU.2 _))
    rw [lintegral_cons k _ hGm]
    have hpw_m : Measurable (fun ξ' : Fin k → ℝ => ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')) :=
      ENNReal.measurable_ofReal.comp (meas_pathWeight hD (n + 1) σ')
    have hinner : ∀ z : ℝ,
        ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D n (Fin.cons i σ') (Fin.cons z ξ')) *
            ENNReal.ofReal (truncCost D α n U x (Fin.cons i σ') (Fin.cons z ξ'))
            ∂(Measure.pi fun _ => volume) =
        (ENNReal.ofReal c₀ * ENNReal.ofReal (D.P i (σ' 0)) * ENNReal.ofReal (D.φ n i z) *
          ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')
            ∂(Measure.pi fun _ => volume)) +
        (ENNReal.ofReal α * ENNReal.ofReal (D.P i (σ' 0)) * (ENNReal.ofReal (D.φ n i z) *
          ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ') *
            ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i z) (x + u₀ - z) σ' ξ')
            ∂(Measure.pi fun _ => volume))) := by
      intro z
      have hU' := shiftPolicy_admissible hU i z
      have hpoint : ∀ ξ' : Fin k → ℝ,
          ENNReal.ofReal (pathWeight D n (Fin.cons i σ') (Fin.cons z ξ')) *
              ENNReal.ofReal (truncCost D α n U x (Fin.cons i σ') (Fin.cons z ξ')) =
          (ENNReal.ofReal c₀ * ENNReal.ofReal (D.P i (σ' 0)) * ENNReal.ofReal (D.φ n i z)) *
              ENNReal.ofReal (pathWeight D (n + 1) σ' ξ') +
          (ENNReal.ofReal α * ENNReal.ofReal (D.P i (σ' 0)) * ENNReal.ofReal (D.φ n i z)) *
              (ENNReal.ofReal (pathWeight D (n + 1) σ' ξ') *
                ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i z) (x + u₀ - z) σ' ξ')) := by
        intro ξ'
        rw [pathWeight_cons, truncCost_cons]
        have hPφ := mul_nonneg (P_nonneg hD i (σ' 0)) (φ_nonneg hD n i z)
        have htc_nn := truncCost_nonneg hD hα0.le (n + 1) (shiftPolicy U i z) hU'.1 (x + u₀ - z) σ' ξ'
        rw [ENNReal.ofReal_mul hPφ, ENNReal.ofReal_mul (P_nonneg hD i (σ' 0)),
            ENNReal.ofReal_add hc₀_nn (mul_nonneg hα0.le htc_nn),
            ENNReal.ofReal_mul hα0.le]
        ring
      simp_rw [hpoint]
      have htc_m : Measurable (fun ξ' : Fin k → ℝ =>
          ENNReal.ofReal (pathWeight D (n + 1) σ' ξ') *
            ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i z) (x + u₀ - z) σ' ξ')) :=
        hpw_m.mul (ENNReal.measurable_ofReal.comp (meas_truncCost hD α (n + 1) _ _ hU'.2 σ'))
      rw [lintegral_add_left (hpw_m.const_mul _), lintegral_const_mul _ hpw_m,
          lintegral_const_mul _ htc_m]
      ring
    simp_rw [hinner]
    have hA_m : Measurable (fun z : ℝ =>
        ENNReal.ofReal c₀ * ENNReal.ofReal (D.P i (σ' 0)) * ENNReal.ofReal (D.φ n i z) *
          ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')
            ∂(Measure.pi fun _ => volume)) :=
      (((ENNReal.measurable_ofReal.comp (φ_meas hD n i)).const_mul _).mul_const _)
    have hB_inner_m : Measurable (fun z : ℝ => ENNReal.ofReal (D.φ n i z) *
        ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ') *
          ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i z) (x + u₀ - z) σ' ξ')
          ∂(Measure.pi fun _ => volume)) := by
      refine (ENNReal.measurable_ofReal.comp (φ_meas hD n i)).mul ?_
      have hjoint : Measurable (fun p : ℝ × (Fin k → ℝ) =>
          ENNReal.ofReal (pathWeight D (n + 1) σ' p.2) *
            ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i p.1) (x + u₀ - p.1) σ' p.2)) := by
        refine (hpw_m.comp measurable_snd).mul (ENNReal.measurable_ofReal.comp ?_)
        have hcons_m : Measurable (fun p : ℝ × (Fin k → ℝ) => (Fin.cons p.1 p.2 : Fin (k + 1) → ℝ)) := by
          have : (fun p : ℝ × (Fin k → ℝ) => (Fin.cons p.1 p.2 : Fin (k + 1) → ℝ)) =
              (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).symm := by
            funext p; exact (cons_symm_eq k p).symm
          rw [this]
          exact MeasurableEquiv.measurable _
        have htot : Measurable (fun p : ℝ × (Fin k → ℝ) =>
            (truncCost D α n U x (Fin.cons i σ') (Fin.cons p.1 p.2) - c₀) / α) :=
          (((meas_truncCost hD α n U x hU.2 _).comp hcons_m).sub measurable_const).div_const α
        have heq_f : (fun p : ℝ × (Fin k → ℝ) =>
            truncCost D α (n + 1) (shiftPolicy U i p.1) (x + u₀ - p.1) σ' p.2) =
            (fun p : ℝ × (Fin k → ℝ) =>
              (truncCost D α n U x (Fin.cons i σ') (Fin.cons p.1 p.2) - c₀) / α) := by
          funext p
          rw [truncCost_cons]
          have hαne : α ≠ 0 := hα0.ne'
          field_simp [c₀, u₀]
          ring
        rw [heq_f]
        exact htot
      exact hjoint.lintegral_prod_right'
    rw [lintegral_add_left hA_m, lintegral_const_mul _ hB_inner_m]
    congr 1
    have mφ : Measurable (fun z : ℝ => ENNReal.ofReal (D.φ n i z)) :=
      ENNReal.measurable_ofReal.comp (φ_meas hD n i)
    calc ∫⁻ z : ℝ, ENNReal.ofReal c₀ * ENNReal.ofReal (D.P i (σ' 0)) * ENNReal.ofReal (D.φ n i z) *
            ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')
              ∂(Measure.pi fun _ => volume)
        = (ENNReal.ofReal c₀ * ENNReal.ofReal (D.P i (σ' 0)) *
            ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')
              ∂(Measure.pi fun _ => volume)) * ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) := by
          rw [← lintegral_const_mul _ mφ]
          refine lintegral_congr (fun z => by ring)
      _ = _ := by rw [φ_lint hD n i, mul_one]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  congr 1
  · -- First sum equals `ENNReal.ofReal c₀`
    rw [sum_group_head]
    have hgrp : ∀ j : Fin L,
        (∑ σ' : Fin (k + 1) → Fin L, if σ' 0 = j then
          ENNReal.ofReal c₀ * ENNReal.ofReal (D.P i (σ' 0)) *
            ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')
              ∂(Measure.pi fun _ => volume) else 0) =
        ENNReal.ofReal c₀ * ENNReal.ofReal (D.P i j) := by
      intro j
      have : (∑ σ' : Fin (k + 1) → Fin L, if σ' 0 = j then
          ENNReal.ofReal c₀ * ENNReal.ofReal (D.P i (σ' 0)) *
            ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')
              ∂(Measure.pi fun _ => volume) else 0) =
          (ENNReal.ofReal c₀ * ENNReal.ofReal (D.P i j)) *
            ∑ σ' : Fin (k + 1) → Fin L, if σ' 0 = j then
              ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')
                ∂(Measure.pi fun _ => volume) else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun σ' _ => ?_)
        split_ifs with h
        · rw [h]
        · simp
      rw [this, weight_sum hD k (n + 1) j, mul_one]
    simp_rw [hgrp]
    rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => P_nonneg hD i j),
        P_sum hD i, ENNReal.ofReal_one, mul_one]
  · -- Second sum equals `ENNReal.ofReal α * ∑ j, ...`
    rw [sum_group_head, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hmeas_σ' : ∀ σ' : Fin (k + 1) → Fin L,
        Measurable (fun z : ℝ => if σ' 0 = j then
          ENNReal.ofReal (D.φ n i z) *
            ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ') *
              ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i z) (x + u₀ - z) σ' ξ')
              ∂(Measure.pi fun _ => volume) else 0) := by
      intro σ'
      by_cases h : σ' 0 = j
      · simp only [if_pos h]
        refine (ENNReal.measurable_ofReal.comp (φ_meas hD n i)).mul ?_
        have hpw_m : Measurable (fun ξ' : Fin k → ℝ => ENNReal.ofReal (pathWeight D (n + 1) σ' ξ')) :=
          ENNReal.measurable_ofReal.comp (meas_pathWeight hD (n + 1) σ')
        have hcons_m : Measurable (fun p : ℝ × (Fin k → ℝ) => (Fin.cons p.1 p.2 : Fin (k + 1) → ℝ)) := by
          have : (fun p : ℝ × (Fin k → ℝ) => (Fin.cons p.1 p.2 : Fin (k + 1) → ℝ)) =
              (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).symm := by
            funext p; exact (cons_symm_eq k p).symm
          rw [this]
          exact MeasurableEquiv.measurable _
        have hjoint : Measurable (fun p : ℝ × (Fin k → ℝ) =>
            ENNReal.ofReal (pathWeight D (n + 1) σ' p.2) *
              ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i p.1) (x + u₀ - p.1) σ' p.2)) := by
          refine (hpw_m.comp measurable_snd).mul (ENNReal.measurable_ofReal.comp ?_)
          have htot : Measurable (fun p : ℝ × (Fin k → ℝ) =>
              (truncCost D α n U x (Fin.cons i σ') (Fin.cons p.1 p.2) - c₀) / α) :=
            (((meas_truncCost hD α n U x hU.2 _).comp hcons_m).sub measurable_const).div_const α
          have heq_f : (fun p : ℝ × (Fin k → ℝ) =>
              truncCost D α (n + 1) (shiftPolicy U i p.1) (x + u₀ - p.1) σ' p.2) =
              (fun p : ℝ × (Fin k → ℝ) =>
                (truncCost D α n U x (Fin.cons i σ') (Fin.cons p.1 p.2) - c₀) / α) := by
            funext p
            rw [truncCost_cons]
            have hαne : α ≠ 0 := hα0.ne'
            field_simp [c₀, u₀]
            ring
          rw [heq_f]
          exact htot
        exact hjoint.lintegral_prod_right'
      · simp only [if_neg h]; exact measurable_const
    have hpull : (∑ σ' : Fin (k + 1) → Fin L, if σ' 0 = j then
        ENNReal.ofReal α * ENNReal.ofReal (D.P i (σ' 0)) *
          ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) *
            ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ') *
              ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i z) (x + u₀ - z) σ' ξ')
              ∂(Measure.pi fun _ => volume) else 0) =
        ENNReal.ofReal α * (ENNReal.ofReal (D.P i j) *
          ∑ σ' : Fin (k + 1) → Fin L, ∫⁻ z : ℝ, if σ' 0 = j then
            ENNReal.ofReal (D.φ n i z) *
              ∫⁻ ξ' : Fin k → ℝ, ENNReal.ofReal (pathWeight D (n + 1) σ' ξ') *
                ENNReal.ofReal (truncCost D α (n + 1) (shiftPolicy U i z) (x + u₀ - z) σ' ξ')
                ∂(Measure.pi fun _ => volume) else 0) := by
      rw [← mul_assoc, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun σ' _ => ?_)
      split_ifs with h
      · rw [h]
      · simp
    rw [hpull, ← lintegral_finsetSum _ (fun σ' _ => hmeas_σ' σ')]
    congr 2
    refine lintegral_congr (fun z => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ' _ => ?_)
    split_ifs <;> simp

lemma meas_fbSurplus (û : ℕ → Fin L → ℝ → ℝ) (hûm : ∀ m j, Measurable (û m j)) (n : ℕ) (x : ℝ) :
    ∀ t (σ : Fin (t + 1) → Fin L), Measurable (fbSurplus û n x t σ) := by
  intro t
  induction t with
  | zero => intro σ; exact measurable_const
  | succ t ih =>
    intro σ
    have h1 := (ih (Fin.init σ)).comp meas_init
    exact (h1.add ((hûm (n + t) _).comp h1)).sub (measurable_pi_apply _)

lemma feedback_admissible (û : ℕ → Fin L → ℝ → ℝ)
    (hû0 : ∀ m j y, 0 ≤ û m j y) (hûm : ∀ m j, Measurable (û m j)) (n : ℕ) (x : ℝ) :
    Admissible (feedback û n x) :=
  ⟨fun t σ ξ => hû0 (n + t) (σ (Fin.last t)) (fbSurplus û n x t σ ξ),
   fun t σ => (hûm (n + t) (σ (Fin.last t))).comp (meas_fbSurplus û hûm n x t σ)⟩

lemma fbSurplus_cons (û : ℕ → Fin L → ℝ → ℝ) (n : ℕ) (x : ℝ) (i : Fin L) (z : ℝ) :
    ∀ t (σ' : Fin (t + 1) → Fin L) (ξ' : Fin t → ℝ),
      fbSurplus û n x (t + 1) (Fin.cons i σ') (Fin.cons z ξ') =
        fbSurplus û (n + 1) (x + û n i x - z) t σ' ξ' := by
  intro t
  induction t with
  | zero =>
    intro σ' ξ'
    simp only [fbSurplus, init_cons_zero]
    rfl
  | succ t ih =>
    intro σ' ξ'
    conv_lhs => rw [fbSurplus]
    conv_rhs => rw [fbSurplus]
    rw [init_cons, init_cons, cons_last_succ, ih (Fin.init σ') (Fin.init ξ'), cons_last_succ]
    have hadd : n + (t + 1) = (n + 1) + t := by omega
    rw [hadd]

lemma shiftPolicy_feedback (û : ℕ → Fin L → ℝ → ℝ) (n : ℕ) (x : ℝ) (i : Fin L) (z : ℝ) :
    shiftPolicy (feedback û n x) i z = feedback û (n + 1) (x + û n i x - z) := by
  funext t σ' ξ'
  simp only [shiftPolicy, feedback, fbSurplus_cons, cons_last_succ]
  have hadd : n + (t + 1) = (n + 1) + t := by omega
  rw [hadd]

lemma feedback_zero_apply (û : ℕ → Fin L → ℝ → ℝ) (n : ℕ) (x : ℝ) (i : Fin L) :
    feedback û n x 0 (fun _ => i) Fin.elim0 = û n i x := by
  simp [feedback, fbSurplus]

/-! ### Section 4: Bellman lower bound and feedback upper bound -/

lemma dpTrunc_le_Jtrunc {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ k n i x (U : Policy L), Admissible U →
      ENNReal.ofReal (dpTrunc D α n k i x) ≤ Jtrunc D α n k i x U := by
  intro k
  induction k with
  | zero =>
    intro n i x U _
    simp [dpTrunc]
  | succ k ih =>
    intro n i x U hU
    rw [Jtrunc_cons hD hα0 n k i x U hU]
    set u₀ := U 0 (fun _ => i) Fin.elim0
    have hu₀ : 0 ≤ u₀ := hU.1 0 _ _
    have hstep :
        ENNReal.ofReal (D.f n i x + orderCost D n i u₀) +
        ENNReal.ofReal α * ENNReal.ofReal (Fnext D n (dpTrunc D α (n + 1) k) i (x + u₀)) ≤
        ENNReal.ofReal (D.f n i x + orderCost D n i u₀) +
        ENNReal.ofReal α * ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
          ∫⁻ z : ℝ, ENNReal.ofReal (D.φ n i z) *
            Jtrunc D α (n + 1) k j (x + u₀ - z) (shiftPolicy U i z) := by
      rw [ofReal_Fnext hD n _ (dpTrunc_measurable hD hα0 hα1 (n + 1) k)
            (dpTrunc_nonneg hD hα0 hα1 (n + 1) k) (dpTrunc_growth hD hα0 hα1 (n + 1) k)]
      gcongr with j _ z
      exact ih (n + 1) j (x + u₀ - z) (shiftPolicy U i z) (shiftPolicy_admissible hU i z)
    have hcombine :
        ENNReal.ofReal (D.f n i x + orderCost D n i u₀) +
        ENNReal.ofReal α * ENNReal.ofReal (Fnext D n (dpTrunc D α (n + 1) k) i (x + u₀)) =
        ENNReal.ofReal (D.f n i x + (orderCost D n i u₀ +
          α * Fnext D n (dpTrunc D α (n + 1) k) i (x + u₀))) := by
      have h1 : 0 ≤ D.f n i x + orderCost D n i u₀ :=
        add_nonneg (f_nonneg hD n i x) (orderCost_nonneg hD hu₀)
      have h2 : 0 ≤ α * Fnext D n (dpTrunc D α (n + 1) k) i (x + u₀) :=
        mul_nonneg hα0.le (Fnext_nonneg hD n _ (dpTrunc_nonneg hD hα0 hα1 (n + 1) k) i _)
      rw [← ENNReal.ofReal_mul hα0.le, ← ENNReal.ofReal_add h1 h2]
      ring_nf
    have hbdd : BddBelow (Set.range (fun u : {u : ℝ // 0 ≤ u} =>
        orderCost D n i u + α * Fnext D n (dpTrunc D α (n + 1) k) i (x + u))) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨u, rfl⟩
      exact add_nonneg (orderCost_nonneg hD u.2)
        (mul_nonneg hα0.le (Fnext_nonneg hD n _ (dpTrunc_nonneg hD hα0 hα1 (n + 1) k) i _))
    have hinf : dpTrunc D α n (k + 1) i x ≤
        D.f n i x + (orderCost D n i u₀ + α * Fnext D n (dpTrunc D α (n + 1) k) i (x + u₀)) := by
      show D.f n i x + ⨅ u : {u : ℝ // 0 ≤ u},
        (orderCost D n i u + α * Fnext D n (dpTrunc D α (n + 1) k) i (x + u)) ≤ _
      linarith [ciInf_le hbdd (⟨u₀, hu₀⟩ : {u : ℝ // 0 ≤ u})]
    calc ENNReal.ofReal (dpTrunc D α n (k + 1) i x)
        ≤ ENNReal.ofReal (D.f n i x + (orderCost D n i u₀ +
            α * Fnext D n (dpTrunc D α (n + 1) k) i (x + u₀))) :=
          ENNReal.ofReal_le_ofReal hinf
      _ = ENNReal.ofReal (D.f n i x + orderCost D n i u₀) +
          ENNReal.ofReal α * ENNReal.ofReal (Fnext D n (dpTrunc D α (n + 1) k) i (x + u₀)) :=
          hcombine.symm
      _ ≤ _ := hstep

lemma dpTrunc_le_vTrunc {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n k : ℕ) (i : Fin L) (x : ℝ) :
    ENNReal.ofReal (dpTrunc D α n k i x) ≤ vTrunc D α n k i x :=
  le_iInf₂ (fun U hU => dpTrunc_le_Jtrunc hD hα0 hα1 k n i x U hU)

lemma Jtrunc_zero (D : Model L) (α : ℝ) (n : ℕ) (i : Fin L) (x : ℝ) (U : Policy L) :
    Jtrunc D α n 0 i x U = 0 := by
  unfold Jtrunc truncCost; simp

lemma Jtrunc_feedback_le_add {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (N : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (û : ℕ → Fin L → ℝ → ℝ)
    (hû0 : ∀ m j y, 0 ≤ û m j y) (hûm : ∀ m j, Measurable (û m j))
    (hopt : ∀ m < N, ∀ i x,
      orderCost D m i (û m i x) +
          α * Fnext D m (dpTrunc D α (m + 1) (N - 1 - m)) i (x + û m i x) ≤
        (⨅ u : {u : ℝ // 0 ≤ u},
          (orderCost D m i u +
            α * Fnext D m (dpTrunc D α (m + 1) (N - 1 - m)) i (x + u))) + δ) :
    ∀ k m, m + k = N → ∀ i x,
      Jtrunc D α m k i x (feedback û m x) ≤ ENNReal.ofReal (dpTrunc D α m k i x + (k : ℝ) * δ) := by
  intro k
  induction k with
  | zero =>
    intro m _ i x
    rw [Jtrunc_zero]
    simp [dpTrunc]
  | succ k ih =>
    intro m hmk i x
    have hmN : m < N := by omega
    have hrem : N - 1 - m = k := by omega
    rw [Jtrunc_cons hD hα0 m k i x (feedback û m x) (feedback_admissible û hû0 hûm m x),
        feedback_zero_apply]
    simp_rw [shiftPolicy_feedback]
    have hcont :
        ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
          ∫⁻ z : ℝ, ENNReal.ofReal (D.φ m i z) *
            Jtrunc D α (m + 1) k j (x + û m i x - z) (feedback û (m + 1) (x + û m i x - z)) ≤
        ENNReal.ofReal (Fnext D m (dpTrunc D α (m + 1) k) i (x + û m i x)) +
          ENNReal.ofReal ((k : ℝ) * δ) := by
      have h1 :
          ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
            ∫⁻ z : ℝ, ENNReal.ofReal (D.φ m i z) *
              Jtrunc D α (m + 1) k j (x + û m i x - z) (feedback û (m + 1) (x + û m i x - z)) ≤
          ∑ j : Fin L, ENNReal.ofReal (D.P i j) *
            ∫⁻ z : ℝ, ENNReal.ofReal (D.φ m i z) *
              (ENNReal.ofReal (dpTrunc D α (m + 1) k j (x + û m i x - z)) +
                ENNReal.ofReal ((k : ℝ) * δ)) := by
        gcongr with j _ z
        have hih := ih (m + 1) (by omega) j (x + û m i x - z)
        exact hih.trans (ENNReal.ofReal_add_le)
      have h2 : ∀ j : Fin L,
          ∫⁻ z : ℝ, ENNReal.ofReal (D.φ m i z) *
              (ENNReal.ofReal (dpTrunc D α (m + 1) k j (x + û m i x - z)) +
                ENNReal.ofReal ((k : ℝ) * δ)) =
          (∫⁻ z : ℝ, ENNReal.ofReal (D.φ m i z) *
              ENNReal.ofReal (dpTrunc D α (m + 1) k j (x + û m i x - z))) +
            ENNReal.ofReal ((k : ℝ) * δ) := by
        intro j
        have hm1 : Measurable (fun z : ℝ => ENNReal.ofReal (D.φ m i z) *
            ENNReal.ofReal (dpTrunc D α (m + 1) k j (x + û m i x - z))) :=
          (ENNReal.measurable_ofReal.comp (φ_meas hD m i)).mul
            (ENNReal.measurable_ofReal.comp
              ((dpTrunc_measurable hD hα0 hα1 (m + 1) k j).comp (measurable_const.sub measurable_id)))
        have hmul : ∀ z, ENNReal.ofReal (D.φ m i z) *
            (ENNReal.ofReal (dpTrunc D α (m + 1) k j (x + û m i x - z)) +
              ENNReal.ofReal ((k : ℝ) * δ)) =
            ENNReal.ofReal (D.φ m i z) *
              ENNReal.ofReal (dpTrunc D α (m + 1) k j (x + û m i x - z)) +
            ENNReal.ofReal ((k : ℝ) * δ) * ENNReal.ofReal (D.φ m i z) := fun z => by ring
        simp_rw [hmul]
        have hmφ : Measurable (fun z : ℝ => ENNReal.ofReal (D.φ m i z)) :=
          ENNReal.measurable_ofReal.comp (φ_meas hD m i)
        rw [lintegral_add_left hm1,
            lintegral_const_mul (ENNReal.ofReal ((k : ℝ) * δ)) hmφ,
            φ_lint hD m i, mul_one]
      simp_rw [h2] at h1
      calc _ ≤ ∑ j : Fin L, (ENNReal.ofReal (D.P i j) *
            (∫⁻ z : ℝ, ENNReal.ofReal (D.φ m i z) *
              ENNReal.ofReal (dpTrunc D α (m + 1) k j (x + û m i x - z))) +
            ENNReal.ofReal (D.P i j) * ENNReal.ofReal ((k : ℝ) * δ)) := by
            simpa only [mul_add] using h1
        _ = (∑ j : Fin L, ENNReal.ofReal (D.P i j) *
              ∫⁻ z : ℝ, ENNReal.ofReal (D.φ m i z) *
                ENNReal.ofReal (dpTrunc D α (m + 1) k j (x + û m i x - z))) +
            (∑ j : Fin L, ENNReal.ofReal (D.P i j)) * ENNReal.ofReal ((k : ℝ) * δ) := by
            rw [Finset.sum_add_distrib, Finset.sum_mul]
        _ = ENNReal.ofReal (Fnext D m (dpTrunc D α (m + 1) k) i (x + û m i x)) +
            ENNReal.ofReal ((k : ℝ) * δ) := by
            rw [← ofReal_Fnext hD m _ (dpTrunc_measurable hD hα0 hα1 (m + 1) k)
                  (dpTrunc_nonneg hD hα0 hα1 (m + 1) k) (dpTrunc_growth hD hα0 hα1 (m + 1) k),
                ← ENNReal.ofReal_sum_of_nonneg (fun j _ => P_nonneg hD i j),
                P_sum hD i, ENNReal.ofReal_one, one_mul]
    have hopt' := hopt m hmN i x
    rw [hrem] at hopt'
    have h1nn : 0 ≤ D.f m i x + orderCost D m i (û m i x) :=
      add_nonneg (f_nonneg hD m i x) (orderCost_nonneg hD (hû0 m i x))
    have h2nn : 0 ≤ Fnext D m (dpTrunc D α (m + 1) k) i (x + û m i x) :=
      Fnext_nonneg hD m _ (dpTrunc_nonneg hD hα0 hα1 (m + 1) k) i _
    have h3nn : 0 ≤ (k : ℝ) * δ := mul_nonneg (Nat.cast_nonneg k) hδ
    calc _ ≤ ENNReal.ofReal (D.f m i x + orderCost D m i (û m i x)) +
          ENNReal.ofReal α * (ENNReal.ofReal (Fnext D m (dpTrunc D α (m + 1) k) i (x + û m i x)) +
            ENNReal.ofReal ((k : ℝ) * δ)) := by gcongr
      _ = ENNReal.ofReal (D.f m i x + orderCost D m i (û m i x) +
            α * (Fnext D m (dpTrunc D α (m + 1) k) i (x + û m i x) + (k : ℝ) * δ)) := by
          rw [← ENNReal.ofReal_add h2nn h3nn, ← ENNReal.ofReal_mul hα0.le,
              ← ENNReal.ofReal_add h1nn (mul_nonneg hα0.le (add_nonneg h2nn h3nn))]
      _ ≤ ENNReal.ofReal (dpTrunc D α m (k + 1) i x + ((k + 1 : ℕ) : ℝ) * δ) := by
          refine ENNReal.ofReal_le_ofReal ?_
          show D.f m i x + orderCost D m i (û m i x) +
              α * (Fnext D m (dpTrunc D α (m + 1) k) i (x + û m i x) + (k : ℝ) * δ) ≤
            D.f m i x + (⨅ u : {u : ℝ // 0 ≤ u},
              (orderCost D m i u + α * Fnext D m (dpTrunc D α (m + 1) k) i (x + u))) +
              ((k + 1 : ℕ) : ℝ) * δ
          have hαk : α * ((k : ℝ) * δ) ≤ (k : ℝ) * δ := by nlinarith
          push_cast
          linarith

/-! ### Section 5: Piecewise-constant ε-optimal selector (Parts 1, 2, 3) -/

lemma exists_eps_selector {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (m k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : Fin L → ℝ → ℝ,
      (∀ i x, 0 ≤ u i x) ∧ (∀ i, Measurable (u i)) ∧
      ∀ i x,
        orderCost D m i (u i x) + α * Fnext D m (dpTrunc D α (m + 1) k) i (x + u i x) ≤
          (⨅ v : {v : ℝ // 0 ≤ v},
            (orderCost D m i v + α * Fnext D m (dpTrunc D α (m + 1) k) i (x + v))) + δ := by
  have hLipNN : 0 ≤ D.C / (1 - α) := div_nonneg (C_pos hD).le (by linarith)
  set K_lip := α * (D.C / (1 - α))
  have hKnn : 0 ≤ K_lip := mul_nonneg hα0.le hLipNN
  set η := δ / (4 * (K_lip + 1))
  have hη : 0 < η := div_pos hδ (by linarith)
  set g : Fin L → ℝ → ℝ := fun i y => α * Fnext D m (dpTrunc D α (m + 1) k) i y
  have hg_nn : ∀ i y, 0 ≤ g i y := fun i y =>
    mul_nonneg hα0.le (Fnext_nonneg hD m _ (dpTrunc_nonneg hD hα0 hα1 (m + 1) k) i y)
  have hg_lip : ∀ i y y', |g i y' - g i y| ≤ K_lip * |y' - y| := fun i y y' => by
    show |α * Fnext D m _ i y' - α * Fnext D m _ i y| ≤ _
    rw [← mul_sub, abs_mul, abs_of_pos hα0]
    have := Fnext_lipschitz hD m _ (dpTrunc_measurable hD hα0 hα1 (m + 1) k)
      (dpTrunc_nonneg hD hα0 hα1 (m + 1) k) (dpTrunc_growth hD hα0 hα1 (m + 1) k)
      hLipNN (dpTrunc_lipschitz hD hα0 hα1 (m + 1) k) i y y'
    calc α * |Fnext D m _ i y' - Fnext D m _ i y| ≤ α * ((D.C / (1 - α)) * |y' - y|) :=
          mul_le_mul_of_nonneg_left this hα0.le
      _ = _ := by ring
  set H : Fin L → ℝ → ℝ := fun i x =>
    ⨅ v : {v : ℝ // 0 ≤ v}, (orderCost D m i v + g i (x + v))
  have hbdd : ∀ i x, BddBelow (Set.range (fun v : {v : ℝ // 0 ≤ v} =>
      orderCost D m i v + g i (x + v))) := fun i x =>
    ⟨0, by rintro _ ⟨v, rfl⟩; exact add_nonneg (orderCost_nonneg hD v.2) (hg_nn i _)⟩
  have hH_lip : ∀ i x x', H i x' - H i x ≤ K_lip * |x' - x| := by
    intro i x x'
    have : H i x' - K_lip * |x' - x| ≤ H i x := by
      refine le_ciInf (fun v => ?_)
      have h1 : H i x' ≤ orderCost D m i v + g i (x' + v) := ciInf_le (hbdd i x') v
      have h2 := (abs_le.mp (hg_lip i (x + v) (x' + v))).2
      have heq : (x' + v.1) - (x + v.1) = x' - x := by ring
      rw [heq] at h2
      linarith
    linarith
  have hgrid : ∀ (i : Fin L) (q : ℤ), ∃ v : ℝ, 0 ≤ v ∧
      orderCost D m i v + g i ((q : ℝ) * η + v) < H i ((q : ℝ) * η) + δ / 2 := by
    intro i q
    have hlt : H i ((q : ℝ) * η) < H i ((q : ℝ) * η) + δ / 2 := by linarith
    obtain ⟨v, hv⟩ := exists_lt_of_ciInf_lt hlt
    exact ⟨v.1, v.2, hv⟩
  choose uq huq0 huqopt using hgrid
  refine ⟨fun i x => uq i ⌊x / η⌋, fun i x => huq0 i ⌊x / η⌋, fun i => ?_, fun i x => ?_⟩
  · exact measurable_from_top.comp (Int.measurable_floor.comp (measurable_id.div_const η))
  · set q : ℤ := ⌊x / η⌋
    set xq : ℝ := (q : ℝ) * η
    have hq1 : (q : ℝ) ≤ x / η := Int.floor_le (x / η)
    have hq2 : x / η < (q : ℝ) + 1 := Int.lt_floor_add_one (x / η)
    have hx1 : xq ≤ x := by
      have := mul_le_mul_of_nonneg_right hq1 hη.le
      rwa [div_mul_cancel₀ _ hη.ne'] at this
    have hx2 : x < xq + η := by
      have := mul_lt_mul_of_pos_right hq2 hη
      rw [div_mul_cancel₀ _ hη.ne', add_mul, one_mul] at this
      exact this
    have hdist : |x - xq| ≤ η := by
      rw [abs_of_nonneg (by linarith)]; linarith
    have hdist' : |xq - x| ≤ η := by rw [abs_sub_comm]; exact hdist
    have h1 := (abs_le.mp (hg_lip i (xq + uq i q) (x + uq i q))).2
    have heq : (x + uq i q) - (xq + uq i q) = x - xq := by ring
    rw [heq] at h1
    have h2 := huqopt i q
    have h3 := hH_lip i x xq
    have h4 : 2 * K_lip * η ≤ δ / 2 := by
      have hpos : 0 < 4 * (K_lip + 1) := by linarith
      have : 2 * K_lip * η = (2 * K_lip / (4 * (K_lip + 1))) * δ := by
        dsimp [η]; ring
      rw [this]
      have hfrac : 2 * K_lip / (4 * (K_lip + 1)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 2)]
        linarith
      nlinarith
    have hKdist : K_lip * |x - xq| ≤ K_lip * η := mul_le_mul_of_nonneg_left hdist hKnn
    have hKdist' : K_lip * |xq - x| ≤ K_lip * η := mul_le_mul_of_nonneg_left hdist' hKnn
    linarith

theorem vTrunc_eq_ofReal_dpTrunc {D : Model L} (hD : Standing D) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (n k : ℕ) (i : Fin L) (x : ℝ) :
    vTrunc D α n k i x = ENNReal.ofReal (dpTrunc D α n k i x) := by
  apply le_antisymm _ (dpTrunc_le_vTrunc hD hα0 hα1 n k i x)
  have hle_eps : ∀ ε : ℝ, 0 < ε →
      vTrunc D α n k i x ≤ ENNReal.ofReal (dpTrunc D α n k i x + ε) := by
    intro ε hε
    set N := n + k
    set δ := ε / ((k : ℝ) + 1)
    have hδ : 0 < δ := div_pos hε (by positivity)
    have hsel : ∀ m : ℕ, ∃ u : Fin L → ℝ → ℝ,
        (∀ j y, 0 ≤ u j y) ∧ (∀ j, Measurable (u j)) ∧
        (m < N → ∀ j y,
          orderCost D m j (u j y) +
              α * Fnext D m (dpTrunc D α (m + 1) (N - 1 - m)) j (y + u j y) ≤
            (⨅ v : {v : ℝ // 0 ≤ v},
              (orderCost D m j v +
                α * Fnext D m (dpTrunc D α (m + 1) (N - 1 - m)) j (y + v))) + δ) := by
      intro m
      obtain ⟨u, hu0, hum, huopt⟩ := exists_eps_selector hD hα0 hα1 m (N - 1 - m) hδ
      exact ⟨u, hu0, hum, fun _ => huopt⟩
    choose û hû0 hûm hûopt using hsel
    have hadm := feedback_admissible û hû0 hûm n x
    have hfb := Jtrunc_feedback_le_add hD hα0 hα1 N hδ.le û hû0 hûm
      (fun m hm => hûopt m hm) k n rfl i x
    have hkδ : (k : ℝ) * δ ≤ ε := by
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have : (k : ℝ) * δ = ((k : ℝ) / ((k : ℝ) + 1)) * ε := by dsimp [δ]; ring
      rw [this]
      have hfrac : (k : ℝ) / ((k : ℝ) + 1) ≤ 1 := by rw [div_le_one hk1]; linarith
      nlinarith
    calc vTrunc D α n k i x
        ≤ Jtrunc D α n k i x (feedback û n x) :=
          iInf₂_le (f := fun U (_ : Admissible U) => Jtrunc D α n k i x U) _ hadm
      _ ≤ ENNReal.ofReal (dpTrunc D α n k i x + (k : ℝ) * δ) := hfb
      _ ≤ ENNReal.ofReal (dpTrunc D α n k i x + ε) := ENNReal.ofReal_le_ofReal (by linarith)
  have hfin : vTrunc D α n k i x ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hle_eps 1 one_pos)
  have htr : (vTrunc D α n k i x).toReal ≤ dpTrunc D α n k i x := by
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hle_eps ε hε)
    have hnn : 0 ≤ dpTrunc D α n k i x + ε :=
      add_nonneg (dpTrunc_nonneg hD hα0 hα1 n k i x) hε.le
    rwa [ENNReal.toReal_ofReal hnn] at h1
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal htr

lemma vTrunc_inC1 {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n k : ℕ) : InC1 (fun i x => (vTrunc D α n k i x).toReal) := by
  have heq : (fun i x => (vTrunc D α n k i x).toReal) = dpTrunc D α n k := by
    funext i x
    rw [vTrunc_eq_ofReal_dpTrunc hD hα0 hα1 n k i x,
        ENNReal.toReal_ofReal (dpTrunc_nonneg hD hα0 hα1 n k i x)]
  rw [heq]
  obtain ⟨Cb, hCb, hgr⟩ := dpTrunc_growth hD hα0 hα1 n k
  refine ⟨⟨⟨dpTrunc_nonneg hD hα0 hα1 n k,
      ⟨fun _ => dpTrunc D α n k,
       fun _ i => dpTrunc_continuous hD hα0 hα1 n k i,
       fun _ i x => dpTrunc_nonneg hD hα0 hα1 n k i x,
       fun _ _ => tendsto_const_nhds⟩⟩,
    ⟨Cb + 1, by linarith, fun i x => by
      have := hgr i x
      have : 0 ≤ 1 + |x| := by positivity
      nlinarith⟩⟩,
    fun i => lipschitz_uniformContinuous (div_nonneg (C_pos hD).le (by linarith))
      (dpTrunc_lipschitz hD hα0 hα1 n k i)⟩

/-! ### Section 6: Measurable exact minimizer under `Cond42 D` (Part 4) -/

/-- For any continuous coercive `G : ℝ → ℝ` and `K ≥ 0`, there is a measurable selector
`u(x) ≥ 0` minimizing `K δ(u) + G(x + u)` over `u ≥ 0`. -/
lemma measurable_argmin_coercive {K : ℝ} (hK : 0 ≤ K) {G : ℝ → ℝ}
    (hGc : Continuous G) (hGtop : Tendsto G atTop atTop) :
    ∃ u : ℝ → ℝ, (∀ x, 0 ≤ u x) ∧ Measurable u ∧
      ∀ x (v : ℝ), 0 ≤ v →
        K * delta (u x) + G (x + u x) ≤ K * delta v + G (x + v) := by
  set mFun : ℝ → ℝ := fun x => sInf (G '' Set.Ici x)
  -- Attainment of `inf_{y ≥ x} G(y)` via compactness
  have hatt : ∀ x : ℝ, ∃ y₀ : ℝ, x ≤ y₀ ∧ ∀ y : ℝ, x ≤ y → G y₀ ≤ G y := by
    intro x
    obtain ⟨R, hR⟩ := eventually_atTop.mp (hGtop.eventually_ge_atTop (G x + 1))
    set R' := max x R
    have hxR' : x ≤ R' := le_max_left x R
    have hne : (Set.Icc x R').Nonempty := ⟨x, le_rfl, hxR'⟩
    obtain ⟨y₀, hy₀mem, hy₀min⟩ := isCompact_Icc.exists_isMinOn hne hGc.continuousOn
    refine ⟨y₀, hy₀mem.1, fun y hy => ?_⟩
    rcases le_or_gt y R' with hle | hgt
    · exact hy₀min ⟨hy, hle⟩
    · have h1 : G x + 1 ≤ G y := hR y ((le_max_right x R).trans hgt.le)
      have h2 : G y₀ ≤ G x := hy₀min ⟨le_rfl, hxR'⟩
      linarith
  have hm_bdd : ∀ x, BddBelow (G '' Set.Ici x) := by
    intro x
    obtain ⟨y₀, _, hy₀⟩ := hatt x
    exact ⟨G y₀, by rintro _ ⟨y, hy, rfl⟩; exact hy₀ y hy⟩
  have hm_le : ∀ x y, x ≤ y → mFun x ≤ G y := fun x y hy =>
    csInf_le (hm_bdd x) ⟨y, hy, rfl⟩
  have hm_att : ∀ x, ∃ y₀, x ≤ y₀ ∧ G y₀ = mFun x := by
    intro x
    obtain ⟨y₀, hx0, hy₀⟩ := hatt x
    refine ⟨y₀, hx0, le_antisymm ?_ (hm_le x y₀ hx0)⟩
    refine le_csInf ⟨G x, x, Set.mem_Ici.mpr le_rfl, rfl⟩ ?_
    rintro _ ⟨y, hy, rfl⟩
    exact hy₀ y hy
  have hm_mono : Monotone mFun := by
    intro x₁ x₂ hx
    exact csInf_le_csInf (hm_bdd x₁) ⟨G x₂, x₂, Set.mem_Ici.mpr le_rfl, rfl⟩
      (Set.image_mono (Set.Ici_subset_Ici.mpr hx))
  set A : ℝ → Set ℝ := fun x => {y : ℝ | x ≤ y ∧ G y = mFun x}
  set yStar : ℝ → ℝ := fun x => sInf (A x)
  have hA_ne : ∀ x, (A x).Nonempty := fun x => hm_att x
  have hA_bdd : ∀ x, BddBelow (A x) := fun x => ⟨x, fun y hy => hy.1⟩
  have hA_closed : ∀ x, IsClosed (A x) := fun x =>
    isClosed_Ici.inter (isClosed_singleton.preimage hGc)
  have hyStar_mem : ∀ x, yStar x ∈ A x := fun x => by
    have hcl := csInf_mem_closure (hA_ne x) (hA_bdd x)
    rwa [(hA_closed x).closure_eq] at hcl
  have hyStar_mono : Monotone yStar := by
    intro x₁ x₂ hx
    rcases lt_or_ge (yStar x₁) x₂ with hlt | hge
    · exact hlt.le.trans (hyStar_mem x₂).1
    · have h1 : mFun x₂ ≤ mFun x₁ := by
        calc mFun x₂ ≤ G (yStar x₁) := hm_le x₂ (yStar x₁) hge
          _ = mFun x₁ := (hyStar_mem x₁).2
      have heq : mFun x₁ = mFun x₂ := le_antisymm (hm_mono hx) h1
      have hmem : yStar x₂ ∈ A x₁ :=
        ⟨hx.trans (hyStar_mem x₂).1, (hyStar_mem x₂).2.trans heq.symm⟩
      exact csInf_le (hA_bdd x₁) hmem
  set u : ℝ → ℝ := fun x => if G x ≤ K + mFun x then 0 else yStar x - x
  have hu_nn : ∀ x, 0 ≤ u x := fun x => by
    dsimp [u]
    split_ifs
    · exact le_rfl
    · linarith [(hyStar_mem x).1]
  have hu_meas : Measurable u := by
    dsimp [u]
    refine Measurable.ite ?_ measurable_const (hyStar_mono.measurable.sub measurable_id)
    exact measurableSet_le hGc.measurable (measurable_const.add hm_mono.measurable)
  refine ⟨u, hu_nn, hu_meas, fun x v hv => ?_⟩
  have hval : K * delta (u x) + G (x + u x) = min (G x) (K + mFun x) := by
    dsimp [u]
    split_ifs with hle
    · simp only [delta_zero, mul_zero, zero_add, add_zero]
      exact (min_eq_left hle).symm
    · push Not at hle
      have hlt : x < yStar x := by
        refine lt_of_le_of_ne (hyStar_mem x).1 (fun heq => ?_)
        have hGx : G x = mFun x := (congrArg G heq).trans (hyStar_mem x).2
        linarith
      have hpos : 0 < yStar x - x := by linarith
      rw [delta_pos hpos, mul_one, add_sub_cancel, (hyStar_mem x).2, min_eq_right hle.le]
  rw [hval]
  rcases eq_or_lt_of_le hv with rfl | hvpos
  · simp only [delta_zero, mul_zero, zero_add, add_zero]
    exact min_le_left _ _
  · rw [delta_pos hvpos, mul_one]
    have h1 : mFun x ≤ G (x + v) := hm_le x (x + v) (by linarith)
    exact (min_le_right _ _).trans (by linarith)

lemma exists_exact_selector {D : Model L} (hD : Standing D) (h42 : Cond42 D)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (m k : ℕ) :
    ∃ u : Fin L → ℝ → ℝ,
      (∀ i x, 0 ≤ u i x) ∧ (∀ i, Measurable (u i)) ∧
      ∀ i x,
        orderCost D m i (u i x) + α * Fnext D m (dpTrunc D α (m + 1) k) i (x + u i x) ≤
          (⨅ v : {v : ℝ // 0 ≤ v},
            (orderCost D m i v + α * Fnext D m (dpTrunc D α (m + 1) k) i (x + v))) + 0 := by
  cases k with
  | zero =>
    refine ⟨fun _ _ => 0, fun _ _ => le_rfl, fun _ => measurable_const, fun i x => ?_⟩
    have hF0 : ∀ y, Fnext D m (dpTrunc D α (m + 1) 0) i y = 0 := fun y => by
      simp [Fnext, dpTrunc]
    simp only [hF0, mul_zero, add_zero, orderCost_zero]
    exact le_ciInf (fun v => orderCost_nonneg hD v.2)
  | succ k' =>
    have hLipNN : 0 ≤ D.C / (1 - α) := div_nonneg (C_pos hD).le (by linarith)
    have hfor : ∀ i : Fin L, ∃ ui : ℝ → ℝ, (∀ x, 0 ≤ ui x) ∧ Measurable ui ∧
        ∀ x (v : ℝ), 0 ≤ v →
          orderCost D m i (ui x) + α * Fnext D m (dpTrunc D α (m + 1) (k' + 1)) i (x + ui x) ≤
            orderCost D m i v + α * Fnext D m (dpTrunc D α (m + 1) (k' + 1)) i (x + v) := by
      intro i
      set g : ℝ → ℝ := fun y => α * Fnext D m (dpTrunc D α (m + 1) (k' + 1)) i y
      set G : ℝ → ℝ := fun y => D.c m i * y + g y
      have hg_lip : ∀ y y', |g y' - g y| ≤ (α * (D.C / (1 - α))) * |y' - y| := fun y y' => by
        show |α * Fnext D m _ i y' - α * Fnext D m _ i y| ≤ _
        rw [← mul_sub, abs_mul, abs_of_pos hα0]
        have := Fnext_lipschitz hD m _ (dpTrunc_measurable hD hα0 hα1 (m + 1) (k' + 1))
          (dpTrunc_nonneg hD hα0 hα1 (m + 1) (k' + 1))
          (dpTrunc_growth hD hα0 hα1 (m + 1) (k' + 1))
          hLipNN (dpTrunc_lipschitz hD hα0 hα1 (m + 1) (k' + 1)) i y y'
        calc α * |Fnext D m _ i y' - Fnext D m _ i y| ≤ α * ((D.C / (1 - α)) * |y' - y|) :=
              mul_le_mul_of_nonneg_left this hα0.le
          _ = _ := by ring
      have hGc : Continuous G :=
        (continuous_const.mul continuous_id).add
          (lipschitz_continuous (mul_nonneg hα0.le hLipNN) hg_lip)
      have hGtop : Tendsto G atTop atTop := by
        have hαtop : Tendsto (fun y => α * (D.c m i * y + Fnext D m (D.f (m + 1)) i y))
            atTop atTop :=
          Filter.Tendsto.const_mul_atTop hα0 (h42 m i)
        refine tendsto_atTop_mono' atTop ?_ hαtop
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
        have hFm : Fnext D m (D.f (m + 1)) i y ≤
            Fnext D m (dpTrunc D α (m + 1) (k' + 1)) i y :=
          Fnext_mono hD m _ _
            (fun j => (f_continuous hD (m + 1) j).measurable) (f_nonneg hD (m + 1))
            ⟨D.C, (C_pos hD).le, f_growth hD (m + 1)⟩
            (dpTrunc_measurable hD hα0 hα1 (m + 1) (k' + 1))
            (dpTrunc_nonneg hD hα0 hα1 (m + 1) (k' + 1))
            (dpTrunc_growth hD hα0 hα1 (m + 1) (k' + 1))
            (dpTrunc_ge_f hD hα0 hα1 (m + 1) k') i y
        have hcy : 0 ≤ D.c m i * y := mul_nonneg (c_nonneg hD m i) hy
        dsimp [G, g]
        nlinarith
      obtain ⟨ui, hui0, huim, huiopt⟩ := measurable_argmin_coercive (K_nonneg hD m i) hGc hGtop
      refine ⟨ui, hui0, huim, fun x v hv => ?_⟩
      have hopt := huiopt x v hv
      simp only [G, orderCost] at hopt ⊢
      linarith [mul_add (D.c m i) x (ui x), mul_add (D.c m i) x v]
    choose u hu0 hum huopt using hfor
    refine ⟨u, hu0, hum, fun i x => ?_⟩
    rw [add_zero]
    exact le_ciInf (fun v => huopt i x v.1 v.2)

theorem truncated_dp_main {L : ℕ} (D : Model L) (α : ℝ) (hD : Standing D) (hα0 : 0 < α)
    (hα1 : α < 1) :
    (∀ n k i x, vTrunc D α n k i x = ENNReal.ofReal (dpTrunc D α n k i x)) ∧
    (∀ n i x, vTrunc D α n 0 i x = 0) ∧
    (∀ n k, InC1 (fun i x => (vTrunc D α n k i x).toReal)) ∧
    (Cond42 D → ∀ n k i x, ∃ U : Policy L, Admissible U ∧
      Jtrunc D α n k i x U = vTrunc D α n k i x) := by
  refine ⟨vTrunc_eq_ofReal_dpTrunc hD hα0 hα1, fun n i x => ?_,
          vTrunc_inC1 hD hα0 hα1, fun h42 n k i x => ?_⟩
  · rw [vTrunc_eq_ofReal_dpTrunc hD hα0 hα1 n 0 i x]
    simp [dpTrunc]
  · set N := n + k
    have hsel : ∀ m : ℕ, ∃ u : Fin L → ℝ → ℝ,
        (∀ j y, 0 ≤ u j y) ∧ (∀ j, Measurable (u j)) ∧
        (m < N → ∀ j y,
          orderCost D m j (u j y) +
              α * Fnext D m (dpTrunc D α (m + 1) (N - 1 - m)) j (y + u j y) ≤
            (⨅ v : {v : ℝ // 0 ≤ v},
              (orderCost D m j v +
                α * Fnext D m (dpTrunc D α (m + 1) (N - 1 - m)) j (y + v))) + 0) := by
      intro m
      obtain ⟨u, hu0, hum, huopt⟩ := exists_exact_selector hD h42 hα0 hα1 m (N - 1 - m)
      exact ⟨u, hu0, hum, fun _ => huopt⟩
    choose û hû0 hûm hûopt using hsel
    refine ⟨feedback û n x, feedback_admissible û hû0 hûm n x, ?_⟩
    apply le_antisymm
    · have hfb := Jtrunc_feedback_le_add hD hα0 hα1 N le_rfl û hû0 hûm
        (fun m hm => hûopt m hm) k n rfl i x
      simpa [vTrunc_eq_ofReal_dpTrunc hD hα0 hα1 n k i x] using hfb
    · exact iInf₂_le (f := fun U (_ : Admissible U) => Jtrunc D α n k i x U) _
        (feedback_admissible û hû0 hûm n x)

end SethiChengSS.Infinite.TruncDP

open SethiChengSS.Infinite in
theorem solution {L : ℕ} (D : Model L) (α : ℝ) (hD : Standing D) (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ n k i x, vTrunc D α n k i x = ENNReal.ofReal (dpTrunc D α n k i x)) ∧
    (∀ n i x, vTrunc D α n 0 i x = 0) ∧
    (∀ n k, InC1 (fun i x => (vTrunc D α n k i x).toReal)) ∧
    (Cond42 D → ∀ n k i x, ∃ U : Policy L, Admissible U ∧
      Jtrunc D α n k i x U = vTrunc D α n k i x) :=
  SethiChengSS.Infinite.TruncDP.truncated_dp_main D α hD hα0 hα1

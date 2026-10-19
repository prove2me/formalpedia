-- Prove2me | solution 1 for QAlgorithms.Nannicini.fdLaplacian_average_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T04:16:34.051421+00:00
-- url     : https://prove2.me/submissions/dbdd5328-3867-473f-a0c4-2bd7ce616d5e

import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Average

set_option autoImplicit false
open MeasureTheory Set QAlgorithms

private lemma interval_cont {g : ℝ → ℝ} {a b c d : ℝ}
    (hg : ContinuousOn g (Icc a b)) (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) :
    IntervalIntegrable g volume c d := by
  apply ContinuousOn.intervalIntegrable (hg.mono ?_)
  exact uIcc_subset_Icc hc hd

private lemma slice_bound (g : ℝ → ℝ) (a b η L : ℝ) (hab : a ≤ b) (hη : 0 < η)
    (hg : ContinuousOn g (Icc (a - η) (b + η)))
    (hLip : ∀ s ∈ Icc (a - η) (b + η), ∀ t ∈ Icc (a - η) (b + η),
      |g s - g t| ≤ L * |s - t|) :
    (∫ t in a..b, (g (t + η) - 2 * g t + g (t - η)) * (η ^ 2)⁻¹) ≤ 2 * L := by
  let h : ℝ → ℝ := fun t => g (t + η) - g t
  have hc : ContinuousOn h (Icc (a - η) b) := by
    apply ContinuousOn.sub
    · exact hg.comp (continuous_id.add continuous_const).continuousOn (by
        intro t ht; constructor <;> (try dsimp) <;> linarith [ht.1, ht.2])
    · exact hg.mono (by intro t ht; constructor <;> linarith [ht.1, ht.2])
  have hint (c d : ℝ) (hc' : c ∈ Icc (a - η) b) (hd' : d ∈ Icc (a - η) b) :=
    interval_cont hc hc' hd'
  have ha : a ∈ Icc (a - η) b := ⟨by linarith, hab⟩
  have hb : b ∈ Icc (a - η) b := ⟨by linarith, le_rfl⟩
  have ham : a - η ∈ Icc (a - η) b := ⟨le_rfl, by linarith⟩
  have hbm : b - η ∈ Icc (a - η) b := ⟨by linarith, by linarith⟩
  have hi := hint a b ha hb
  have hj : IntervalIntegrable (fun t => h (t - η)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hc.comp (continuous_id.sub continuous_const).continuousOn (by
      intro t ht; constructor <;> (try dsimp) <;> linarith [ht.1, ht.2])
  have hid : (∫ t in a..b, g (t + η) - 2 * g t + g (t - η)) =
      (∫ t in (b - η)..b, h t) - ∫ t in (a - η)..a, h t := by
    calc
      _ = ∫ t in a..b, h t - h (t - η) := by
        apply intervalIntegral.integral_congr; intro t ht; dsimp [h]; rw [sub_add_cancel]; ring
      _ = (∫ t in a..b, h t) - ∫ t in (a - η)..(b - η), h t := by
        rw [intervalIntegral.integral_sub hi hj, intervalIntegral.integral_comp_sub_right]
      _ = _ := intervalIntegral.integral_interval_sub_interval_comm' hi
        (hint _ _ ham hbm) (hint _ _ ha ham)
  have hnorm (t : ℝ) (ht : t ∈ Icc (a - η) b) : ‖h t‖ ≤ L * η := by
    have he := hLip (t + η) (by constructor <;> linarith [ht.1, ht.2]) t
      (by constructor <;> linarith [ht.1, ht.2])
    simpa [h, Real.norm_eq_abs, abs_of_pos hη] using he
  have htop := intervalIntegral.norm_integral_le_of_norm_le_const (a := b - η) (b := b)
    (f := h) (C := L * η) (by
      intro t ht; apply hnorm; rw [uIoc_of_le (by linarith)] at ht
      exact ⟨by linarith [ht.1], ht.2⟩)
  have hbot := intervalIntegral.norm_integral_le_of_norm_le_const (a := a - η) (b := a)
    (f := h) (C := L * η) (by
      intro t ht; apply hnorm; rw [uIoc_of_le (by linarith)] at ht
      exact ⟨ht.1.le, ht.2.trans hab⟩)
  have hnum : (∫ t in a..b, g (t + η) - 2 * g t + g (t - η)) ≤ 2 * L * η ^ 2 := by
    rw [hid]
    rw [Real.norm_eq_abs, show b - (b - η) = η by ring, abs_of_pos hη] at htop
    rw [Real.norm_eq_abs, show a - (a - η) = η by ring, abs_of_pos hη] at hbot
    nlinarith [(le_abs_self (∫ t in (b - η)..b, h t)),
      (neg_le_abs (∫ t in (a - η)..a, h t))]
  rw [intervalIntegral.integral_mul_const]
  calc
    _ ≤ (2 * L * η ^ 2) * (η ^ 2)⁻¹ := mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = 2 * L := by field_simp

private lemma lip_cont {d : ℕ} {D : Set (Fin d → ℝ)} (f : (Fin d → ℝ) → ℝ) (L : ℝ)
    (hL : ∀ y ∈ D, ∀ z ∈ D, |f y - f z| ≤ L * Real.sqrt (∑ i, (y i - z i)^2)) :
    ContinuousOn f D := by
  apply (LipschitzOnWith.of_dist_le' (K := |L| * (d + 1 : ℝ)) ?_).continuousOn
  intro y hy z hz
  rw [Real.dist_eq, dist_eq_norm]
  have hn : 0 ≤ ‖y - z‖ := norm_nonneg _
  have hs : ∑ i, (y i - z i)^2 ≤ (d : ℝ) * ‖y - z‖^2 := by
    calc
      _ ≤ ∑ _i : Fin d, ‖y - z‖^2 := by
        apply Finset.sum_le_sum; intro i _
        have hi := norm_le_pi_norm (y-z) i
        simp only [Pi.sub_apply, Real.norm_eq_abs] at hi
        have hi2 := mul_self_le_mul_self (abs_nonneg (y i-z i)) hi
        simpa [← sq, sq_abs] using hi2
      _ = _ := by simp
  have hsqrt : Real.sqrt (∑ i, (y i - z i)^2) ≤ (d + 1 : ℝ) * ‖y-z‖ := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
      nlinarith [sq_nonneg (d : ℝ), sq_nonneg ‖y-z‖]
  calc
    _ ≤ L * Real.sqrt (∑ i, (y i-z i)^2) := hL y hy z hz
    _ ≤ |L| * Real.sqrt (∑ i, (y i-z i)^2) :=
      mul_le_mul_of_nonneg_right (le_abs_self L) (Real.sqrt_nonneg _)
    _ ≤ |L| * ((d + 1 : ℝ) * ‖y-z‖) := mul_le_mul_of_nonneg_left hsqrt (abs_nonneg _)
    _ = _ := by ring

private lemma fiber_bound {n : ℕ} (μ : Fin (n+1) → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] (j : Fin (n+1)) (F : (Fin (n+1) → ℝ) → ℝ)
    (hF : Integrable F (Measure.pi μ)) (C : ℝ)
    (hC : ∀ᵐ y ∂Measure.pi (fun i => μ (j.succAbove i)),
      (∫ t, F (j.insertNth t y) ∂μ j) ≤ C) :
    (∫ z, F z ∂Measure.pi μ) ≤ (Measure.pi (fun i => μ (j.succAbove i))).real univ * C := by
  let ν := Measure.pi (fun i => μ (j.succAbove i))
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) j
  have hm := (measurePreserving_piFinSuccAbove μ j).symm
  have hi : Integrable (fun p : ℝ × (Fin n → ℝ) => F (j.insertNth p.1 p.2)) ((μ j).prod ν) := by
    simpa [e, ν, Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv] using
      (hm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hF
  calc
    _ = ∫ p : ℝ × (Fin n → ℝ), F (j.insertNth p.1 p.2) ∂((μ j).prod ν) := by
      simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv] using
        (hm.integral_comp' F).symm
    _ = ∫ y, ∫ t, F (j.insertNth t y) ∂μ j ∂ν := integral_prod_symm _ hi
    _ ≤ ∫ _y, C ∂ν := integral_mono_ae hi.integral_prod_right (integrable_const C) hC
    _ = _ := by simp [integral_const, smul_eq_mul, ν]

private def cube {d : ℕ} (x : Fin d → ℝ) (r : ℝ) : Set (Fin d → ℝ) :=
  {y | ∀ i, |x i - y i| ≤ r}

private lemma cube_eq {d : ℕ} (x : Fin d → ℝ) (r : ℝ) :
    cube x r = Icc (fun i => x i - r) (fun i => x i + r) := by
  ext y
  simp only [cube, mem_ofPred_eq, abs_le, mem_Icc, Pi.le_def]
  constructor
  · intro h; exact ⟨fun i => by linarith [(h i).2], fun i => by linarith [(h i).1]⟩
  · rintro ⟨h₁,h₂⟩ i; constructor <;> linarith [h₁ i,h₂ i]

private lemma cube_pi {d : ℕ} (x : Fin d → ℝ) (r : ℝ) :
    cube x r = univ.pi (fun i => Icc (x i-r) (x i+r)) := by
  rw [pi_univ_Icc, cube_eq]

private lemma cube_shift {d : ℕ} (x : Fin d → ℝ) (r η : ℝ) (hη : 0 ≤ η)
    (j : Fin d) {z : Fin d → ℝ} (hz : z ∈ cube x r) :
    z + η • Pi.single j 1 ∈ cube x (r+η) ∧ z - η • Pi.single j 1 ∈ cube x (r+η) := by
  constructor <;> intro i
  all_goals
    have hi := (abs_le.mp (hz i))
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs <;> apply abs_le.mpr <;> constructor <;> nlinarith

private lemma insert_shift {n : ℕ} (j : Fin (n+1)) (t η : ℝ) (y : Fin n → ℝ) :
    j.insertNth (t+η) y = j.insertNth t y + η • Pi.single j 1 ∧
    j.insertNth (t-η) y = j.insertNth t y - η • Pi.single j 1 := by
  constructor <;> funext i
  all_goals
    obtain rfl | ⟨k,rfl⟩ := j.eq_self_or_eq_succAbove i
    · simp
    · simp [Fin.succAbove_ne]

private lemma slice_lip {n : ℕ} (x : Fin (n+1) → ℝ) (r η L : ℝ) (hη : 0 ≤ η)
    (f : (Fin (n+1) → ℝ) → ℝ)
    (hL : ∀ y ∈ cube x (r+η), ∀ z ∈ cube x (r+η),
      |f y-f z| ≤ L * Real.sqrt (∑ i, (y i-z i)^2))
    (j : Fin (n+1)) (y : Fin n → ℝ) (hy : y ∈ cube (fun i => x (j.succAbove i)) r) :
    ∀ s ∈ Icc (x j-r-η) (x j+r+η), ∀ t ∈ Icc (x j-r-η) (x j+r+η),
      |f (j.insertNth s y)-f (j.insertNth t y)| ≤ L * |s-t| := by
  have hmem (s : ℝ) (hs : s ∈ Icc (x j-r-η) (x j+r+η)) :
      j.insertNth s y ∈ cube x (r+η) := by
    change ∀ i : Fin (n+1), |x i - j.insertNth (α := fun _ => ℝ) s y i| ≤ r+η
    intro i
    obtain rfl | ⟨k,rfl⟩ := j.eq_self_or_eq_succAbove i
    · simp only [Fin.insertNth_apply_same]
      exact abs_le.mpr ⟨by linarith [hs.2], by linarith [hs.1]⟩
    · simpa only [Fin.insertNth_apply_succAbove] using (hy k).trans (by linarith)
  intro s hs t ht
  have he := hL _ (hmem s hs) _ (hmem t ht)
  have hsum : (∑ i, (j.insertNth s y i - j.insertNth t y i)^2) = (s-t)^2 := by
    rw [Fin.sum_univ_succAbove _ j]
    simp
  simpa only [hsum, Real.sqrt_sq_eq_abs] using he

theorem solution {d : ℕ} (η r L : ℝ) (hη : 0 < η) (hηr : η < r) (x : Fin d → ℝ)
    (f : (Fin d → ℝ) → ℝ) (hf : ConvexOn ℝ {y | ∀ i, |x i - y i| ≤ r + η} f)
    (hL : ∀ y ∈ {y : Fin d → ℝ | ∀ i, |x i - y i| ≤ r + η},
      ∀ y' ∈ {y : Fin d → ℝ | ∀ i, |x i - y i| ≤ r + η},
        |f y - f y'| ≤ L * Real.sqrt (∑ i, (y i - y' i) ^ 2)) :
    ⨍ z in {y : Fin d → ℝ | ∀ i, |x i - y i| ≤ r}, fdLaplacian η f z ≤ d * L / r := by
  classical
  have hr : 0 < r := hη.trans hηr
  cases d with
  | zero => simp [fdLaplacian, average_zero]
  | succ n =>
    change (⨍ z in cube x r, fdLaplacian η f z) ≤ (n+1 : ℕ) * L / r
    have hc := lip_cont f L hL
    let μ : Fin (n+1) → Measure ℝ := fun i => volume.restrict (Icc (x i-r) (x i+r))
    have hμ : volume.restrict (cube x r) = Measure.pi μ := by
      rw [cube_pi]
      exact Measure.restrict_pi_pi (fun _ => volume) _
    have hsub : cube x r ⊆ cube x (r+η) := by
      intro z hz i; exact (hz i).trans (by linarith)
    let F : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ := fun j z =>
      (f (z+η • Pi.single j 1)-2*f z+f (z-η • Pi.single j 1)) * (η^2)⁻¹
    have hF (j : Fin (n+1)) : Integrable (F j) (Measure.pi μ) := by
      rw [←hμ, cube_eq]
      apply ContinuousOn.integrableOn_Icc
      rw [←cube_eq]
      apply ContinuousOn.mul_const
      apply ContinuousOn.add
      · apply ContinuousOn.sub
        · exact hc.comp (continuous_id.add continuous_const).continuousOn (by
            intro z hz; exact (cube_shift x r η hη.le j hz).1)
        · exact continuousOn_const.mul (hc.mono hsub)
      · exact hc.comp (continuous_id.sub continuous_const).continuousOn (by
          intro z hz; exact (cube_shift x r η hη.le j hz).2)
    have hbound (j : Fin (n+1)) :
        (∫ z, F j z ∂Measure.pi μ) ≤ (Measure.pi μ).real univ * (L/r) := by
      let ν := Measure.pi (fun i => μ (j.succAbove i))
      have hs : ∀ᵐ y ∂ν, (∫ t, F j (j.insertNth t y) ∂μ j) ≤ 2*L := by
        have hν : ν = volume.restrict (cube (fun i => x (j.succAbove i)) r) := by
          dsimp [ν, μ]; rw [cube_pi]
          exact (Measure.restrict_pi_pi (fun _ => volume) _).symm
        rw [hν]
        filter_upwards [ae_restrict_mem (by rw [cube_eq]; exact measurableSet_Icc)] with y hy
        have hsl := slice_lip x r η L hη.le f hL j y hy
        have hcont : ContinuousOn (fun t => f (j.insertNth t y))
            (Icc (x j-r-η) (x j+r+η)) := by
          apply (LipschitzOnWith.of_dist_le' (K := L) ?_).continuousOn
          intro s hs t ht; simpa [Real.dist_eq] using hsl s hs t ht
        change (∫ t in Icc (x j-r) (x j+r), F j (j.insertNth t y)) ≤ _
        rw [integral_Icc_eq_integral_Ioc, ←intervalIntegral.integral_of_le (by linarith)]
        have he := slice_bound (fun t => f (j.insertNth t y)) (x j-r) (x j+r) η L
          (by linarith) hη hcont hsl
        simpa only [F, (insert_shift j _ η y).1, (insert_shift j _ η y).2] using he
      have he := fiber_bound μ j (F j) (hF j) (2*L) hs
      have hmass : (Measure.pi μ).real univ = (2*r) * ν.real univ := by
        simp only [Measure.real, Measure.pi_univ, ENNReal.toReal_prod, ν]
        rw [Fin.prod_univ_succAbove _ j]
        congr 1
        simp only [μ, Measure.restrict_apply_univ]
        rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
        ring
      rw [hmass]
      calc
        _ ≤ ν.real univ * (2*L) := he
        _ = 2*r*ν.real univ * (L/r) := by field_simp
    have htotal : (∫ z, fdLaplacian η f z ∂Measure.pi μ) ≤
        (Measure.pi μ).real univ * ((n+1 : ℕ)*L/r) := by
      change (∫ z, ∑ j, F j z ∂Measure.pi μ) ≤ _
      rw [integral_finsetSum _ (fun j _ => hF j)]
      calc
        _ ≤ ∑ _j : Fin (n+1), (Measure.pi μ).real univ * (L/r) :=
          Finset.sum_le_sum (fun j _ => hbound j)
        _ = _ := by simp; ring
    have hmasspos : 0 < (Measure.pi μ).real univ := by
      simp only [Measure.real, Measure.pi_univ, ENNReal.toReal_prod]
      apply Finset.prod_pos
      intro i _
      simp only [μ, Measure.restrict_apply_univ]
      change 0 < (volume (Icc (x i-r) (x i+r))).toReal
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      linarith
    rw [setAverage_eq]
    change (volume.real (cube x r))⁻¹ * _ ≤ _
    have hmass : volume.real (cube x r) = (Measure.pi μ).real univ := by
      change (volume (cube x r)).toReal = ((Measure.pi μ) univ).toReal
      rw [←hμ, Measure.restrict_apply_univ]
    rw [hmass, hμ]
    calc
      _ ≤ ((Measure.pi μ).real univ)⁻¹ *
          ((Measure.pi μ).real univ * ((n+1 : ℕ)*L/r)) :=
        mul_le_mul_of_nonneg_left htotal (by positivity)
      _ = _ := by rw [←mul_assoc, inv_mul_cancel₀ hmasspos.ne', one_mul]

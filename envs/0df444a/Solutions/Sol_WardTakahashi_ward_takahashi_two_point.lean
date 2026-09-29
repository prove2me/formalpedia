-- Prove2me | solution 1 for WardTakahashi.ward_takahashi_two_point
-- status  : ACCEPTED   (prove)
-- author  : @37720879
-- created : 2026-09-28T09:18:44.000685+00:00
-- url     : https://prove2.me/submissions/5291538f-1264-4cb7-85f0-37f9c175ce8e

import Mathlib
import Definitions.Def_WardTakahashi_LatticeU1
import Theorems.Thm_WardTakahashi_noether_current_conservation
import Theorems.Thm_WardTakahashi_local_ward_takahashi

open MeasureTheory Complex WardTakahashi

namespace WardTakahashi

private noncomputable def twoPointObs {N : ℕ} (y z : Fin N) (φ : FieldConfig N) : ℂ :=
  φ y * starRingEnd ℂ (φ z)

private lemma twoPointObs_contDiff {N : ℕ} (y z : Fin N) :
    ContDiff ℝ 1 (twoPointObs y z) := by
  have hy : ContDiff ℝ 1 (fun φ : FieldConfig N => φ y) := contDiff_apply ℝ ℂ y
  have hz : ContDiff ℝ 1 (fun φ : FieldConfig N => starRingEnd ℂ (φ z)) := by
    simpa [Function.comp_def, Complex.conjCLE_apply] using
      (Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ z))
  exact hy.mul hz

private lemma twoPointObs_h1 {N : ℕ} (S : FieldConfig N → ℝ)
    (hS : ContDiff ℝ 1 S)
    (hm : Integrable (fun φ : FieldConfig N =>
      (1 + ‖φ‖ ^ 3) * Real.exp (-S φ))) (y z : Fin N) :
    Integrable (fun φ : FieldConfig N =>
      ‖φ‖ * ‖twoPointObs y z φ‖ * Real.exp (-S φ)) := by
  apply hm.mono'
  · have hcont : Continuous (fun φ : FieldConfig N =>
        ‖φ‖ * ‖twoPointObs y z φ‖ * Real.exp (-S φ)) := by
      have hobs : Continuous (twoPointObs y z) :=
        (twoPointObs_contDiff y z).continuous
      exact ((continuous_id.norm.mul hobs.norm).mul
        (Real.continuous_exp.comp (hS.continuous.neg)))
    exact hcont.aestronglyMeasurable
  · filter_upwards [] with φ
    have hy : ‖φ y‖ ≤ ‖φ‖ := norm_le_pi_norm φ y
    have hz : ‖φ z‖ ≤ ‖φ‖ := norm_le_pi_norm φ z
    have he : 0 ≤ Real.exp (-S φ) := (Real.exp_pos _).le
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) he)]
    have hstar : ‖(starRingEnd ℂ) (φ z)‖ = ‖φ z‖ := by simp
    have hnorm : ‖twoPointObs y z φ‖ ≤ ‖φ‖ ^ 2 := by
      simp only [twoPointObs, norm_mul, hstar]
      calc
        ‖φ y‖ * ‖φ z‖ ≤ ‖φ‖ * ‖φ‖ :=
          mul_le_mul hy hz (norm_nonneg _) (norm_nonneg _)
        _ = ‖φ‖ ^ 2 := by ring
    have hp : ‖φ‖ * ‖twoPointObs y z φ‖ ≤ ‖φ‖ ^ 3 := by
      calc
        ‖φ‖ * ‖twoPointObs y z φ‖ ≤ ‖φ‖ * ‖φ‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
        _ = ‖φ‖ ^ 3 := by ring
    have hval : ‖φ‖ ^ 3 ≤ 1 + ‖φ‖ ^ 3 := by linarith
    exact mul_le_mul_of_nonneg_right (hp.trans hval) he

private lemma twoPointObs_localVar {N : ℕ} (x y z : Fin N) (φ : FieldConfig N) :
    localVar x (twoPointObs y z) φ =
      I * ((if x = y then 1 else 0) - (if x = z then 1 else 0)) * twoPointObs y z φ := by
  let py : FieldConfig N →L[ℝ] ℂ := ContinuousLinearMap.proj y
  let pz : FieldConfig N →L[ℝ] ℂ := ContinuousLinearMap.proj z
  have hy : HasFDerivAt (fun ψ : FieldConfig N => ψ y) py φ :=
    hasFDerivAt_apply y φ
  have hz : HasFDerivAt (fun ψ : FieldConfig N => starRingEnd ℂ (ψ z))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp pz) φ := by
    have h := (Complex.conjCLE.hasFDerivAt.comp φ
      (hasFDerivAt_apply (𝕜 := ℝ) z φ))
    simpa [Function.comp_def, py, pz, Complex.conjCLE_apply] using h
  have hd := hy.mul hz
  have hderiv : localVar x (twoPointObs y z) φ =
      φ y * starRingEnd ℂ ((localGen x φ) z) +
        starRingEnd ℂ (φ z) * (localGen x φ) y := by
    change (fderiv ℝ ((fun ψ : FieldConfig N => ψ y) *
      (fun ψ : FieldConfig N => starRingEnd ℂ (ψ z))) φ) (localGen x φ) = _
    rw [hd.fderiv]
    simp [py, pz]
  rw [hderiv]
  have hgen (w : Fin N) : (localGen x φ) w = if x = w then I * φ w else 0 := by
    by_cases hxw : x = w
    · subst w; simp [localGen]
    · simp [localGen, hxw]
  rw [hgen z, hgen y]
  simp only [twoPointObs]
  split_ifs <;> simp <;> ring

private lemma twoPoint_assemble {N : ℕ} (S : FieldConfig N → ℝ)
    (x y z : Fin N)
    (hconservation : ∀ φ : FieldConfig N, ∑ x', localVar x' S φ = 0)
    (hlocal : pathIntegral S (localVar x (twoPointObs y z)) =
      pathIntegral S (fun φ => twoPointObs y z φ * ((localVar x S φ : ℝ) : ℂ))) :
    (∀ φ : FieldConfig N, ∑ x', localVar x' S φ = 0) ∧
    pathIntegral S (fun φ => ((localVar x S φ : ℝ) : ℂ) *
      (φ y * starRingEnd ℂ (φ z))) =
      I * ((if x = y then 1 else 0) - (if x = z then 1 else 0)) *
        pathIntegral S (fun φ => φ y * starRingEnd ℂ (φ z)) := by
  constructor
  · exact hconservation
  · let c : ℂ := I * ((if x = y then 1 else 0) - (if x = z then 1 else 0))
    have hcontact : pathIntegral S (localVar x (twoPointObs y z)) =
        c * pathIntegral S (twoPointObs y z) := by
      calc
        pathIntegral S (localVar x (twoPointObs y z)) =
            ∫ φ, c * (twoPointObs y z φ * (Real.exp (-S φ) : ℂ)) := by
          simp only [pathIntegral, twoPointObs_localVar, ← mul_assoc]
          rfl
        _ = c * pathIntegral S (twoPointObs y z) := by
          rw [integral_const_mul]
          rfl
    have hcomm : pathIntegral S (fun φ => ((localVar x S φ : ℝ) : ℂ) *
        twoPointObs y z φ) =
        pathIntegral S (fun φ => twoPointObs y z φ *
          ((localVar x S φ : ℝ) : ℂ)) := by
      congr 1
      funext φ
      exact mul_comm _ _
    change pathIntegral S (fun φ => ((localVar x S φ : ℝ) : ℂ) *
      twoPointObs y z φ) = c * pathIntegral S (twoPointObs y z)
    exact hcomm.trans (hlocal.symm.trans hcontact)

private lemma twoPoint_root_of_integrability {N : ℕ} (S : FieldConfig N → ℝ)
    (hS : ContDiff ℝ 1 S) (hinv : IsU1Invariant S) (x y z : Fin N)
    (h1 : Integrable (fun φ : FieldConfig N =>
      ‖φ‖ * ‖twoPointObs y z φ‖ * Real.exp (-S φ)))
    (h2 : Integrable (fun φ : FieldConfig N =>
      ‖φ‖ * ‖fderiv ℝ
        (fun ψ => twoPointObs y z ψ * (Real.exp (-S ψ) : ℂ)) φ‖)) :
    (∀ φ : FieldConfig N, ∑ x', localVar x' S φ = 0) ∧
    pathIntegral S (fun φ => ((localVar x S φ : ℝ) : ℂ) *
      (φ y * starRingEnd ℂ (φ z))) =
      I * ((if x = y then 1 else 0) - (if x = z then 1 else 0)) *
        pathIntegral S (fun φ => φ y * starRingEnd ℂ (φ z)) := by
  apply twoPoint_assemble S x y z
  · intro φ
    exact noether_current_conservation S hS.differentiable_one hinv φ
  · exact local_ward_takahashi S (twoPointObs y z) hS
      (twoPointObs_contDiff y z) x h1 h2

private theorem twoPoint_deriv_apply {N : ℕ} (y z : Fin N)
    (φ v : FieldConfig N) :
    fderiv ℝ (fun ψ : FieldConfig N => ψ y * starRingEnd ℂ (ψ z)) φ v =
      v y * starRingEnd ℂ (φ z) + φ y * starRingEnd ℂ (v z) := by
  let ey : FieldConfig N →L[ℝ] ℂ := ContinuousLinearMap.proj y
  let ez : FieldConfig N →L[ℝ] ℂ := ContinuousLinearMap.proj z
  let cz : FieldConfig N →L[ℝ] ℂ := (conjCLE : ℂ →L[ℝ] ℂ).comp ez
  have hy : HasFDerivAt (fun ψ : FieldConfig N => ψ y) ey φ := by
    convert ey.hasFDerivAt (x := φ) using 1
    funext ψ
    rfl
  have hz : HasFDerivAt (fun ψ : FieldConfig N => starRingEnd ℂ (ψ z)) cz φ := by
    convert cz.hasFDerivAt (x := φ) using 1
    funext ψ
    simp [cz, ez]
  have hp := (hy.mul hz).fderiv
  have hfun : ((fun ψ : FieldConfig N => ψ y) *
      (fun ψ : FieldConfig N => starRingEnd ℂ (ψ z))) =
      (fun ψ : FieldConfig N => ψ y * starRingEnd ℂ (ψ z)) := by
    funext ψ
    rfl
  rw [hfun] at hp
  calc
    (fderiv ℝ (fun ψ : FieldConfig N => ψ y * starRingEnd ℂ (ψ z)) φ) v =
        φ y * starRingEnd ℂ (v z) + starRingEnd ℂ (φ z) * v y := by
      simpa [ey, ez, cz, smul_eq_mul]
        using congrArg (fun L : FieldConfig N →L[ℝ] ℂ => L v) hp
    _ = v y * starRingEnd ℂ (φ z) + φ y * starRingEnd ℂ (v z) := by ring

private theorem weight_deriv_apply {N : ℕ} (S : FieldConfig N → ℝ)
    (hS : ContDiff ℝ 1 S) (φ v : FieldConfig N) :
    fderiv ℝ (fun ψ : FieldConfig N => (Real.exp (-S ψ) : ℂ)) φ v =
      -((Real.exp (-S φ) * fderiv ℝ S φ v : ℝ) : ℂ) := by
  have h := ((hS.differentiable_one φ).hasFDerivAt.neg.exp)
  have hc := (ofRealCLM.hasFDerivAt.comp φ h).fderiv
  have happ := congrArg (fun L : FieldConfig N →L[ℝ] ℂ => L v) hc
  have hfun : ((ofRealCLM : ℝ →L[ℝ] ℂ) ∘
      (fun ψ : FieldConfig N => Real.exp ((-S) ψ))) =
      (fun ψ : FieldConfig N => (Real.exp (-S ψ) : ℂ)) := by
    funext ψ
    rfl
  rw [hfun] at happ
  simpa [ofRealCLM_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using happ

private theorem twoPoint_deriv_norm_le {N : ℕ} (y z : Fin N)
    (φ : FieldConfig N) :
    ‖fderiv ℝ (fun ψ : FieldConfig N => ψ y * starRingEnd ℂ (ψ z)) φ‖ ≤
      2 * ‖φ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [twoPoint_deriv_apply]
  calc
    ‖v y * starRingEnd ℂ (φ z) + φ y * starRingEnd ℂ (v z)‖ ≤
        ‖v y * starRingEnd ℂ (φ z)‖ + ‖φ y * starRingEnd ℂ (v z)‖ :=
      norm_add_le _ _
    _ = ‖v y‖ * ‖φ z‖ + ‖φ y‖ * ‖v z‖ := by simp
    _ ≤ ‖v‖ * ‖φ‖ + ‖φ‖ * ‖v‖ := by
      exact add_le_add
        (mul_le_mul (norm_le_pi_norm v y) (norm_le_pi_norm φ z)
          (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (norm_le_pi_norm φ y) (norm_le_pi_norm v z)
          (norm_nonneg _) (norm_nonneg _))
    _ = (2 * ‖φ‖) * ‖v‖ := by ring

private theorem twoPoint_norm_le_sq {N : ℕ} (y z : Fin N)
    (φ : FieldConfig N) :
    ‖φ y * starRingEnd ℂ (φ z)‖ ≤ ‖φ‖ ^ 2 := by
  have hy : ‖φ y‖ ≤ ‖φ‖ := norm_le_pi_norm φ y
  have hz : ‖φ z‖ ≤ ‖φ‖ := norm_le_pi_norm φ z
  have hstar : ‖(starRingEnd ℂ) (φ z)‖ = ‖φ z‖ := by simp
  rw [norm_mul, hstar]
  calc
    ‖φ y‖ * ‖φ z‖ ≤ ‖φ‖ * ‖φ‖ :=
      mul_le_mul hy hz (norm_nonneg _) (norm_nonneg _)
    _ = ‖φ‖ ^ 2 := by ring

private theorem weight_deriv_norm_le {N : ℕ} (S : FieldConfig N → ℝ)
    (hS : ContDiff ℝ 1 S) (φ : FieldConfig N) :
    ‖fderiv ℝ (fun ψ : FieldConfig N => (Real.exp (-S ψ) : ℂ)) φ‖ ≤
      Real.exp (-S φ) * ‖fderiv ℝ S φ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [weight_deriv_apply S hS φ v]
  calc
    ‖-((Real.exp (-S φ) * fderiv ℝ S φ v : ℝ) : ℂ)‖ =
        Real.exp (-S φ) * ‖fderiv ℝ S φ v‖ := by
      rw [norm_neg, Complex.norm_real, norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (Real.exp_pos _).le]
    _ ≤ Real.exp (-S φ) * (‖fderiv ℝ S φ‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left ((fderiv ℝ S φ).le_opNorm v) (Real.exp_pos _).le
    _ = (Real.exp (-S φ) * ‖fderiv ℝ S φ‖) * ‖v‖ := by ring

private theorem twoPoint_h2 {N : ℕ} (S : FieldConfig N → ℝ)
    (hS : ContDiff ℝ 1 S)
    (hm : Integrable (fun φ : FieldConfig N =>
      (1 + ‖φ‖ ^ 3) * Real.exp (-S φ)))
    (hd : Integrable (fun φ : FieldConfig N =>
      ‖φ‖ ^ 3 * ‖fderiv ℝ S φ‖ * Real.exp (-S φ)))
    (y z : Fin N) :
    Integrable (fun φ : FieldConfig N =>
      ‖φ‖ * ‖fderiv ℝ (fun ψ : FieldConfig N =>
        (ψ y * starRingEnd ℂ (ψ z)) * (Real.exp (-S ψ) : ℂ)) φ‖) := by
  let P : FieldConfig N → ℂ := fun φ => φ y * starRingEnd ℂ (φ z)
  let W : FieldConfig N → ℂ := fun φ => (Real.exp (-S φ) : ℂ)
  let G : FieldConfig N → ℂ := fun φ => P φ * W φ
  have hP : ContDiff ℝ 1 P := by
    have hy : ContDiff ℝ 1 (fun φ : FieldConfig N => φ y) := by
      convert (ContinuousLinearMap.proj y : FieldConfig N →L[ℝ] ℂ).contDiff using 1
      funext φ
      rfl
    have hz : ContDiff ℝ 1 (fun φ : FieldConfig N => starRingEnd ℂ (φ z)) := by
      convert ((conjCLE : ℂ →L[ℝ] ℂ).comp
        (ContinuousLinearMap.proj z : FieldConfig N →L[ℝ] ℂ)).contDiff using 1
      funext φ
      simp
    convert hy.mul hz using 1
  have hW : ContDiff ℝ 1 W := by
    have hr : ContDiff ℝ 1 (fun φ : FieldConfig N => Real.exp (-S φ)) := by
      fun_prop
    convert ofRealCLM.contDiff.comp hr using 1
    funext φ
    rfl
  have hG : ContDiff ℝ 1 G := hP.mul hW
  have hsum : Integrable (fun φ : FieldConfig N =>
      2 * ((1 + ‖φ‖ ^ 3) * Real.exp (-S φ)) +
      ‖φ‖ ^ 3 * ‖fderiv ℝ S φ‖ * Real.exp (-S φ)) :=
    (hm.const_mul (2 : ℝ)).add hd
  apply hsum.mono'
  · have hc : Continuous (fun φ : FieldConfig N => ‖φ‖ * ‖fderiv ℝ G φ‖) := by
      fun_prop (disch := assumption)
    exact hc.aestronglyMeasurable
  · filter_upwards [] with φ
    have he : 0 ≤ Real.exp (-S φ) := (Real.exp_pos _).le
    have hr : 0 ≤ ‖φ‖ := norm_nonneg _
    have hP0 : ‖P φ‖ ≤ ‖φ‖ ^ 2 := by
      simpa [P] using twoPoint_norm_le_sq y z φ
    have hDP : ‖fderiv ℝ P φ‖ ≤ 2 * ‖φ‖ := by
      simpa [P] using twoPoint_deriv_norm_le y z φ
    have hDW : ‖fderiv ℝ W φ‖ ≤ Real.exp (-S φ) * ‖fderiv ℝ S φ‖ := by
      simpa [W] using weight_deriv_norm_le S hS φ
    have hW0 : ‖W φ‖ = Real.exp (-S φ) := by
      change ‖(Real.exp (-S φ) : ℂ)‖ = Real.exp (-S φ)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg he]
    have hDG : ‖fderiv ℝ G φ‖ ≤
        ‖φ‖ ^ 2 * (Real.exp (-S φ) * ‖fderiv ℝ S φ‖) +
        Real.exp (-S φ) * (2 * ‖φ‖) := by
      have hprod := fderiv_fun_mul (hP.differentiable_one φ) (hW.differentiable_one φ)
      change fderiv ℝ G φ = P φ • fderiv ℝ W φ + W φ • fderiv ℝ P φ at hprod
      rw [hprod]
      calc
        ‖P φ • fderiv ℝ W φ + W φ • fderiv ℝ P φ‖ ≤
            ‖P φ • fderiv ℝ W φ‖ + ‖W φ • fderiv ℝ P φ‖ := norm_add_le _ _
        _ = ‖P φ‖ * ‖fderiv ℝ W φ‖ + ‖W φ‖ * ‖fderiv ℝ P φ‖ := by
          simp only [norm_smul]
        _ ≤ ‖φ‖ ^ 2 * (Real.exp (-S φ) * ‖fderiv ℝ S φ‖) +
            Real.exp (-S φ) * (2 * ‖φ‖) := by
          apply add_le_add
          · exact mul_le_mul hP0 hDW (norm_nonneg _) (sq_nonneg _)
          · rw [hW0]
            exact mul_le_mul_of_nonneg_left hDP he
    have hr2 : ‖φ‖ ^ 2 ≤ 1 + ‖φ‖ ^ 3 := by
      rcases le_total ‖φ‖ 1 with h | h
      · have hh : 0 ≤ ‖φ‖ * (1 - ‖φ‖) :=
          mul_nonneg hr (sub_nonneg.mpr h)
        nlinarith
      · have hh : 0 ≤ ‖φ‖ ^ 2 * (‖φ‖ - 1) :=
          mul_nonneg (sq_nonneg _) (sub_nonneg.mpr h)
        nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr (norm_nonneg _))]
    calc
      ‖φ‖ * ‖fderiv ℝ G φ‖ ≤
          ‖φ‖ * (‖φ‖ ^ 2 * (Real.exp (-S φ) * ‖fderiv ℝ S φ‖) +
            Real.exp (-S φ) * (2 * ‖φ‖)) :=
        mul_le_mul_of_nonneg_left hDG hr
      _ = ‖φ‖ ^ 3 * ‖fderiv ℝ S φ‖ * Real.exp (-S φ) +
          (2 * ‖φ‖ ^ 2) * Real.exp (-S φ) := by ring
      _ ≤ ‖φ‖ ^ 3 * ‖fderiv ℝ S φ‖ * Real.exp (-S φ) +
          (2 * (1 + ‖φ‖ ^ 3)) * Real.exp (-S φ) := by
        have hh : (2 * ‖φ‖ ^ 2) * Real.exp (-S φ) ≤
            (2 * (1 + ‖φ‖ ^ 3)) * Real.exp (-S φ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hr2 (by norm_num)) he
        simpa [add_comm] using
          (add_le_add_left hh (‖φ‖ ^ 3 * ‖fderiv ℝ S φ‖ * Real.exp (-S φ)))
      _ = 2 * ((1 + ‖φ‖ ^ 3) * Real.exp (-S φ)) +
          ‖φ‖ ^ 3 * ‖fderiv ℝ S φ‖ * Real.exp (-S φ) := by ring

end WardTakahashi

theorem solution {N : ℕ} (S : FieldConfig N → ℝ)
    (hS : ContDiff ℝ 1 S) (hinv : IsU1Invariant S)
    (hm : Integrable (fun φ : FieldConfig N =>
      (1 + ‖φ‖ ^ 3) * Real.exp (-S φ)))
    (hd : Integrable (fun φ : FieldConfig N =>
      ‖φ‖ ^ 3 * ‖fderiv ℝ S φ‖ * Real.exp (-S φ)))
    (x y z : Fin N) :
    (∀ φ : FieldConfig N, ∑ x', localVar x' S φ = 0) ∧
    pathIntegral S (fun φ => ((localVar x S φ : ℝ) : ℂ) *
      (φ y * starRingEnd ℂ (φ z))) =
      I * ((if x = y then 1 else 0) - (if x = z then 1 else 0)) *
        pathIntegral S (fun φ => φ y * starRingEnd ℂ (φ z)) := by
  have h1 : Integrable (fun φ : FieldConfig N =>
      ‖φ‖ * ‖WardTakahashi.twoPointObs y z φ‖ * Real.exp (-S φ)) :=
    WardTakahashi.twoPointObs_h1 S hS hm y z
  have h2 : Integrable (fun φ : FieldConfig N =>
      ‖φ‖ * ‖fderiv ℝ (fun ψ => WardTakahashi.twoPointObs y z ψ *
        (Real.exp (-S ψ) : ℂ)) φ‖) := by
    simpa [WardTakahashi.twoPointObs] using
      (WardTakahashi.twoPoint_h2 S hS hm hd y z)
  exact WardTakahashi.twoPoint_root_of_integrability S hS hinv x y z h1 h2

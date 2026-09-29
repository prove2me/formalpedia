-- Prove2me | solution 1 for WardTakahashi.local_ward_takahashi
-- status  : ACCEPTED   (prove)
-- author  : @37720879
-- created : 2026-09-28T09:16:31.763261+00:00
-- url     : https://prove2.me/submissions/21ccf9f6-501f-478e-ac53-56f9a1ea711d

import Mathlib
import Definitions.Def_WardTakahashi_LatticeU1
import Theorems.Thm_WardTakahashi_integral_localVar_eq_zero

open MeasureTheory Complex WardTakahashi

theorem solution {N : ℕ} (S : FieldConfig N → ℝ) (F : FieldConfig N → ℂ)
    (hS : ContDiff ℝ 1 S) (hF : ContDiff ℝ 1 F) (x : Fin N)
    (h1 : Integrable (fun φ : FieldConfig N => ‖φ‖ * ‖F φ‖ * Real.exp (-S φ)))
    (h2 : Integrable (fun φ : FieldConfig N =>
      ‖φ‖ * ‖fderiv ℝ (fun ψ => F ψ * (Real.exp (-S ψ) : ℂ)) φ‖)) :
    pathIntegral S (localVar x F) = pathIntegral S
      (fun φ => F φ * ((localVar x S φ : ℝ) : ℂ)) := by
  let G : FieldConfig N → ℂ := fun φ => F φ * (Real.exp (-S φ) : ℂ)
  have hG : ContDiff ℝ 1 G := by
    change ContDiff ℝ 1 (fun φ : FieldConfig N => F φ * (Real.exp (-S φ) : ℂ))
    exact hF.mul (Complex.ofRealCLM.contDiff.comp (hS.neg.exp))
  have h1G : Integrable (fun φ : FieldConfig N => ‖φ‖ * ‖G φ‖) := by
    convert h1 using 1
    funext φ
    simp [G, Complex.norm_exp, mul_assoc]
  have h2G : Integrable (fun φ : FieldConfig N => ‖φ‖ * ‖fderiv ℝ G φ‖) := by
    simpa [G] using h2
  have hzero : ∫ φ, localVar x G φ = 0 :=
    WardTakahashi.integral_localVar_eq_zero G hG x h1G h2G
  have hpoint (φ : FieldConfig N) :
      localVar x G φ =
        localVar x F φ * (Real.exp (-S φ) : ℂ) -
          (F φ * ((localVar x S φ : ℝ) : ℂ)) * (Real.exp (-S φ) : ℂ) := by
    have hs : HasFDerivAt S (fderiv ℝ S φ) φ :=
      (hS.differentiable one_ne_zero φ).hasFDerivAt
    have hw : HasFDerivAt (fun ψ : FieldConfig N => (Real.exp (-S ψ) : ℂ))
        (Complex.ofRealCLM.comp (Real.exp (-S φ) • -(fderiv ℝ S φ))) φ := by
      exact Complex.ofRealCLM.hasFDerivAt.comp φ (hs.neg.exp)
    have hg := (hF.differentiable one_ne_zero φ).hasFDerivAt.mul hw
    change HasFDerivAt G _ φ at hg
    rw [show localVar x G φ = fderiv ℝ G φ (localGen x φ) from rfl,
        show localVar x F φ = fderiv ℝ F φ (localGen x φ) from rfl,
        show localVar x S φ = fderiv ℝ S φ (localGen x φ) from rfl,
        hg.fderiv]
    simp [ContinuousLinearMap.comp_apply, smul_eq_mul]
    ring
  have hlocal : Continuous (localGen x : FieldConfig N → FieldConfig N) := by
    apply continuous_pi
    intro y
    by_cases hxy : x = y
    · subst y
      have hc0 : Continuous (fun φ : FieldConfig N => φ x) := continuous_apply x
      have hc : Continuous (fun φ : FieldConfig N => I * φ x) := hc0.const_mul I
      simpa [localGen] using hc
    · simpa [localGen, hxy] using
        (continuous_const : Continuous (fun _ : FieldConfig N => (0 : ℂ)))
  have hnorm (φ : FieldConfig N) : ‖localGen x φ‖ ≤ ‖φ‖ := by
    calc
      ‖localGen x φ‖ = ‖φ x‖ := by simp [localGen, Pi.norm_single]
      _ ≤ ‖φ‖ := norm_le_pi_norm φ x
  have hC : Integrable (fun φ : FieldConfig N => localVar x G φ) := by
    apply Integrable.mono' h2G
    · have hc : Continuous (fun φ : FieldConfig N => fderiv ℝ G φ (localGen x φ)) :=
        (hG.continuous_fderiv one_ne_zero).clm_apply hlocal
      exact hc.aestronglyMeasurable
    · filter_upwards [] with φ
      change ‖fderiv ℝ G φ (localGen x φ)‖ ≤ ‖φ‖ * ‖fderiv ℝ G φ‖
      calc
        ‖fderiv ℝ G φ (localGen x φ)‖ ≤
            ‖fderiv ℝ G φ‖ * ‖localGen x φ‖ := (fderiv ℝ G φ).le_opNorm _
        _ ≤ ‖fderiv ℝ G φ‖ * ‖φ‖ := by gcongr; exact hnorm φ
        _ = ‖φ‖ * ‖fderiv ℝ G φ‖ := mul_comm _ _
  let A : FieldConfig N → ℂ := fun φ => localVar x F φ * (Real.exp (-S φ) : ℂ)
  let B : FieldConfig N → ℂ :=
    fun φ => (F φ * ((localVar x S φ : ℝ) : ℂ)) * (Real.exp (-S φ) : ℂ)
  have hAB (φ : FieldConfig N) : localVar x G φ = A φ - B φ := hpoint φ
  have hABint : Integrable (fun φ : FieldConfig N => A φ - B φ) := by
    apply hC.congr
    filter_upwards [] with φ
    exact hAB φ
  have hABzero : ∫ φ, A φ - B φ = 0 := by
    calc
      ∫ φ, A φ - B φ = ∫ φ, localVar x G φ := by
        congr 1
        funext φ
        exact (hAB φ).symm
      _ = 0 := hzero
  change ∫ φ, A φ = ∫ φ, B φ
  by_cases hA : Integrable A
  · have hB : Integrable B := by
      have hB' : Integrable (fun φ : FieldConfig N => A φ - (A φ - B φ)) :=
        hA.sub hABint
      have heq : (fun φ : FieldConfig N => A φ - (A φ - B φ)) = B := by
        funext φ
        abel
      rwa [heq] at hB'
    rw [integral_sub hA hB] at hABzero
    exact sub_eq_zero.mp hABzero
  · have hB : ¬ Integrable B := by
      intro hB
      apply hA
      have hA' : Integrable (fun φ : FieldConfig N => (A φ - B φ) + B φ) :=
        hABint.add hB
      have heq : (fun φ : FieldConfig N => (A φ - B φ) + B φ) = A := by
        funext φ
        abel
      rwa [heq] at hA'
    rw [integral_undef hA, integral_undef hB]

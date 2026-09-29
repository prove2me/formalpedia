-- Prove2me | solution 1 for SZFilaments.centralDensity_of_meanComptonY
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:52:47.879532+00:00
-- url     : https://prove2.me/submissions/1b1f7708-5c50-4ca9-a6cb-ca2b166e9b0a

import Definitions.Def_szFilamentModel

open MeasureTheory Real
open SZFilaments

theorem W4b_SZFilaments_gaussC (C : ℝ) (hC : 0 < C) :
    ∫ l : ℝ, Real.exp (-l ^ 2 / (2 * C)) = Real.sqrt (2 * π) * Real.sqrt C := by
  have e1 : (fun l : ℝ => Real.exp (-l ^ 2 / (2 * C))) =
      fun l => Real.exp (-(1 / (2 * C)) * l ^ 2) := by
    funext l; congr 1; ring
  rw [e1, integral_gaussian]
  have e2 : π / (1 / (2 * C)) = (2 * π) * C := by rw [div_div_eq_mul_div, div_one]; ring
  rw [e2, Real.sqrt_mul (by positivity)]

theorem W4b_SZFilaments_intProfile (n0 sigma sigmaB r : ℝ) (hsigma : 0 < sigma) :
    ∫ l : ℝ, gaussianFilamentProfile n0 sigma sigmaB l r =
      Real.sqrt (2 * π) * n0 * sigma * Real.exp (-r ^ 2 / (2 * (sigma ^ 2 + sigmaB ^ 2))) := by
  have e : (fun l => gaussianFilamentProfile n0 sigma sigmaB l r) =
      fun l => (n0 * Real.exp (-r ^ 2 / (2 * (sigma ^ 2 + sigmaB ^ 2)))) *
        Real.exp (-l ^ 2 / (2 * sigma ^ 2)) := by
    funext l; simp only [gaussianFilamentProfile]; ring
  rw [e, integral_const_mul, W4b_SZFilaments_gaussC (sigma ^ 2) (by positivity),
    Real.sqrt_sq hsigma.le]
  ring

theorem W4b_SZFilaments_comptonY_gaussianFilamentProfile
    (n0 sigma sigmaB kB Te sigmaT me c r : ℝ) (hsigma : 0 < sigma) :
    comptonY (szPrefactor kB Te sigmaT me c)
        (fun l => gaussianFilamentProfile n0 sigma sigmaB l r)
      = Real.sqrt (2 * π) * n0 * sigma * (kB * Te * sigmaT / (me * c ^ 2)) *
          Real.exp (-r ^ 2 / (2 * (sigma ^ 2 + sigmaB ^ 2))) := by
  unfold comptonY
  rw [W4b_SZFilaments_intProfile n0 sigma sigmaB r hsigma]
  unfold szPrefactor
  ring

theorem solution
    (n0 sigma sigmaB kB Te sigmaT me c ybar : ℝ) (hsigma : 0 < sigma)
    (hkB : 0 < kB) (hTe : 0 < Te) (hsigmaT : 0 < sigmaT) (hme : 0 < me) (hc : 0 < c)
    (hy : comptonY (szPrefactor kB Te sigmaT me c)
        (fun l => gaussianFilamentProfile n0 sigma sigmaB l 0) = ybar / 0.9) :
    n0 = ybar / 0.9 * (me * c ^ 2 / (kB * Te * sigmaT)) / (Real.sqrt (2 * π) * sigma) := by
  unfold comptonY at hy
  rw [W4b_SZFilaments_intProfile n0 sigma sigmaB 0 hsigma] at hy
  have hexp : Real.exp (-(0 : ℝ) ^ 2 / (2 * (sigma ^ 2 + sigmaB ^ 2))) = 1 := by simp
  rw [hexp] at hy
  unfold szPrefactor at hy
  have hS : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  have h1 : 0 < kB * Te * sigmaT := by positivity
  have h2 : 0 < me * c ^ 2 := by positivity
  have := hS.ne'; have := h1.ne'; have := h2.ne'; have := hsigma.ne'
  rw [← hy]
  field_simp <;> ring

theorem W4b_SZFilaments_totalElectrons_gaussianFilamentProfile
    (L n0 sigma sigmaB kB Te sigmaT me c ybar : ℝ) (hsigma : 0 < sigma)
    (hkB : 0 < kB) (hTe : 0 < Te) (hsigmaT : 0 < sigmaT) (hme : 0 < me) (hc : 0 < c)
    (hy : comptonY (szPrefactor kB Te sigmaT me c)
        (fun l => gaussianFilamentProfile n0 sigma sigmaB l 0) = ybar / 0.9) :
    totalElectrons L (fun l r => gaussianFilamentProfile n0 sigma sigmaB l r)
      = ybar / 0.9 * (me * c ^ 2 / (kB * Te * sigmaT)) * Real.sqrt (2 * π) * L *
          Real.sqrt (sigma ^ 2 + sigmaB ^ 2) := by
  have hn0 := solution n0 sigma sigmaB kB Te sigmaT me c
    ybar hsigma hkB hTe hsigmaT hme hc hy
  unfold totalElectrons
  have e : (fun r => ∫ l : ℝ, gaussianFilamentProfile n0 sigma sigmaB l r) =
      fun r => (Real.sqrt (2 * π) * n0 * sigma) *
        Real.exp (-r ^ 2 / (2 * (sigma ^ 2 + sigmaB ^ 2))) := by
    funext r; rw [W4b_SZFilaments_intProfile n0 sigma sigmaB r hsigma]
  rw [e, integral_const_mul, W4b_SZFilaments_gaussC (sigma ^ 2 + sigmaB ^ 2) (by positivity)]
  have hS : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  have h1 : 0 < kB * Te * sigmaT := by positivity
  have h2 : 0 < me * c ^ 2 := by positivity
  have := hS.ne'; have := h1.ne'; have := h2.ne'; have := hsigma.ne'
  rw [hn0]
  field_simp <;> ring

theorem W4b_SZFilaments_centralDensityContrast_of_meanConvergence
    (delta0 sigma sigmaB H0 Om c a DL DS kappabar : ℝ) (hsigma : 0 < sigma)
    (hH0 : 0 < H0) (hOm : 0 < Om) (hc : 0 < c) (ha : 0 < a)
    (hDL : 0 < DL) (hDLS : DL < DS)
    (hkappa : convergence (lensingPrefactor H0 Om c a DL DS)
        (fun l => gaussianFilamentProfile delta0 sigma sigmaB l 0) = kappabar / 0.9) :
    delta0 = kappabar / 0.9 / (Real.sqrt (2 * π) * sigma) *
        (2 * a * c ^ 2 / (3 * H0 ^ 2 * Om)) * (DS / (DL * (DS - DL))) := by
  unfold convergence at hkappa
  rw [W4b_SZFilaments_intProfile delta0 sigma sigmaB 0 hsigma] at hkappa
  have hexp : Real.exp (-(0 : ℝ) ^ 2 / (2 * (sigma ^ 2 + sigmaB ^ 2))) = 1 := by simp
  rw [hexp] at hkappa
  unfold lensingPrefactor at hkappa
  have hS : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  have hDS : 0 < DS := by linarith
  have hD : 0 < DS - DL := by linarith
  have := hS.ne'; have := hsigma.ne'; have := hH0.ne'; have := hOm.ne'; have := hc.ne'
  have := ha.ne'; have := hDL.ne'; have := hDS.ne'; have := hD.ne'
  rw [← hkappa]
  field_simp <;> ring

theorem W4b_SZFilaments_sqrt_sq_add_sq_beam_bounds (sigma sigmaB : ℝ) (hsigma : 0 < sigma)
    (hsigmaB : 0 < sigmaB) :
    sigmaB ≤ Real.sqrt (sigma ^ 2 + sigmaB ^ 2) ∧
      Real.sqrt (sigma ^ 2 + sigmaB ^ 2) ≤ sigmaB * (1 + sigma ^ 2 / (2 * sigmaB ^ 2)) := by
  constructor
  · calc sigmaB = Real.sqrt (sigmaB ^ 2) := (Real.sqrt_sq hsigmaB.le).symm
      _ ≤ Real.sqrt (sigma ^ 2 + sigmaB ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  · have hB' : sigmaB ≠ 0 := hsigmaB.ne'
    set t := sigma ^ 2 / (2 * sigmaB) with ht
    have hY : sigmaB * (1 + sigma ^ 2 / (2 * sigmaB ^ 2)) = sigmaB + t := by
      rw [ht]; field_simp <;> ring
    have h2 : 2 * sigmaB * t = sigma ^ 2 := by
      rw [ht]; field_simp <;> ring
    have hnn : 0 ≤ sigmaB + t := by
      have : 0 ≤ t := by rw [ht]; positivity
      linarith
    rw [hY]
    calc Real.sqrt (sigma ^ 2 + sigmaB ^ 2) ≤ Real.sqrt ((sigmaB + t) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])
      _ = sigmaB + t := Real.sqrt_sq hnn

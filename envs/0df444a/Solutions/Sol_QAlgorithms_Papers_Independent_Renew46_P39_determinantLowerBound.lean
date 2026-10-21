-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P39.determinantLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T01:07:18.885179+00:00
-- url     : https://prove2.me/submissions/72b09f54-2d67-4f83-b761-bccb7e316ecb

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P39
noncomputable section

open Filter

open scoped BigOperators Topology ENNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Renew46.P39

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsDensity IsTraceClass traceSize rankOne)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov FockIndex DensityKernel GaussianWithCovariance standardFormCovariance
   modeCovarianceBlock productWeyl weylArgument CharacteristicSummable
   multimodeWeylTrace covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Frontier30.P08
  (QuadratureIndex interleavedSymplecticForm isSymplectic)

open QAlgorithms.Papers.Independent.Dependency50.P10
  (physicalCovariance supportInverse)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (unitaryCoeff conjugateKernel boundedUnitaryConjugation)


theorem g64n_psd2 (p1 p2 p3 : ℝ) (h : ∀ u v : ℝ, 0 ≤ p1 * u ^ 2 + 2 * p2 * u * v + p3 * v ^ 2) :
    0 ≤ p1 ∧ 0 ≤ p3 ∧ p2 ^ 2 ≤ p1 * p3 := by
  have h1 := h 1 0
  have h3 := h 0 1
  have ha := h p3 (-p2)
  have hb := h (-p2) p1
  have hc := h 1 1
  have hd := h 1 (-1)
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  rcases lt_or_eq_of_le (show 0 ≤ p1 by nlinarith) with hp1 | hp1
  · nlinarith
  rcases lt_or_eq_of_le (show 0 ≤ p3 by nlinarith) with hp3 | hp3
  · nlinarith
  subst hp1; subst hp3
  have : p2 = 0 := by nlinarith
  subst this; simp

theorem g64n_mink2 (p1 p2 p3 m1 m2 m3 : ℝ) (hp1 : 0 ≤ p1) (hp3 : 0 ≤ p3) (hp : p2 ^ 2 ≤ p1 * p3)
    (hm1 : 0 ≤ m1) (hm3 : 0 ≤ m3) (hm : m2 ^ 2 ≤ m1 * m3) :
    0 ≤ p1 * m3 + p3 * m1 - 2 * p2 * m2 ∧
    4 * ((p1 * p3 - p2 ^ 2) * (m1 * m3 - m2 ^ 2)) ≤ (p1 * m3 + p3 * m1 - 2 * p2 * m2) ^ 2 := by
  set P := p1 * p3 with hP
  set M := m1 * m3 with hM
  have hP0 : 0 ≤ P := mul_nonneg hp1 hp3
  have hM0 : 0 ≤ M := mul_nonneg hm1 hm3
  set s := Real.sqrt (P * M) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = P * M := Real.sq_sqrt (mul_nonneg hP0 hM0)
  have hA0 : 0 ≤ p1 * m3 + p3 * m1 := by positivity
  have hA : 2 * s ≤ p1 * m3 + p3 * m1 := by
    have : (2 * s) ^ 2 ≤ (p1 * m3 + p3 * m1) ^ 2 := by nlinarith [sq_nonneg (p1 * m3 - p3 * m1)]
    by_contra hc; have hc := not_le.mp hc; nlinarith
  have hB : p2 * m2 ≤ s := by
    have : (p2 * m2) ^ 2 ≤ s ^ 2 := by
      rw [hs2]; nlinarith [sq_nonneg p2, sq_nonneg m2, mul_le_mul hp hm (sq_nonneg _) (by positivity)]
    by_contra hc; have hc := not_le.mp hc; nlinarith
  have hC : 2 * s * (p2 * m2) ≤ P * m2 ^ 2 + p2 ^ 2 * M := by
    have h1 : 0 ≤ P * m2 ^ 2 + p2 ^ 2 * M := by positivity
    have h2 : (2 * s * (p2 * m2)) ^ 2 ≤ (P * m2 ^ 2 + p2 ^ 2 * M) ^ 2 := by
      have : (2 * s * (p2 * m2)) ^ 2 = 4 * (P * M) * (p2 ^ 2 * m2 ^ 2) := by rw [← hs2]; ring
      rw [this]; nlinarith [sq_nonneg (P * m2 ^ 2 - p2 ^ 2 * M)]
    by_contra hc; have hc := not_le.mp hc; nlinarith
  refine ⟨by nlinarith, ?_⟩
  have hD : 0 ≤ s - p2 * m2 := by linarith
  have hE : 2 * (s - p2 * m2) ≤ p1 * m3 + p3 * m1 - 2 * p2 * m2 := by linarith
  have hF : 4 * (s - p2 * m2) ^ 2 ≤ (p1 * m3 + p3 * m1 - 2 * p2 * m2) ^ 2 := by nlinarith
  have hG : (P - p2 ^ 2) * (M - m2 ^ 2) ≤ (s - p2 * m2) ^ 2 := by nlinarith
  linarith

def g64n_dG (a1 a2 a3 b1 b2 b3 c1 c2 c3 c4 : ℝ) : ℝ :=
  a1*a3*b1*b3 - a1*a3*b2*b2 - a1*c3*c3*b3 + a1*c3*b2*c4 + a1*c4*c3*b2 - a1*c4*b1*c4 - a2*a2*b1*b3 + a2*a2*b2*b2 + a2*c3*c1*b3 - a2*c3*b2*c2 - a2*c4*c1*b2 + a2*c4*b1*c2 + c1*a2*c3*b3 - c1*a2*b2*c4 - c1*a3*c1*b3 + c1*a3*b2*c2 + c1*c4*c1*c4 - c1*c4*c3*c2 - c2*a2*c3*b2 + c2*a2*b1*c4 + c2*a3*c1*b2 - c2*a3*b1*c2 - c2*c3*c1*c4 + c2*c3*c3*c2

theorem g64n_corePD (a1 a2 a3 b1 b2 b3 c1 c2 c3 c4 : ℝ)
    (hQ : ∀ x1 x2 y1 y2 : ℝ, 0 ≤ a1*x1^2 + 2*a2*x1*x2 + a3*x2^2 + b1*y1^2 + 2*b2*y1*y2 + b3*y2^2 +
      2*(c1*x1*y1 + c2*x1*y2 + c3*x2*y1 + c4*x2*y2))
    (hA : 0 < a1 * a3 - a2 ^ 2) :
    let dG := g64n_dG a1 a2 a3 b1 b2 b3 c1 c2 c3 c4
    let X := (a1 * a3 - a2 ^ 2) * (b1 * b3 - b2 ^ 2) - dG - (c1 * c4 - c2 * c3) ^ 2
    0 ≤ dG ∧ 0 ≤ X ∧ 4 * dG * (c1 * c4 - c2 * c3) ^ 2 ≤ X ^ 2 := by
  intro dG X
  set dA := a1 * a3 - a2 ^ 2 with hdA
  set m1 := a3*c1^2 - 2*a2*c1*c3 + a1*c3^2
  set m2 := a3*c1*c2 - a2*c1*c4 - a2*c2*c3 + a1*c3*c4
  set m3 := a3*c2^2 - 2*a2*c2*c4 + a1*c4^2
  set s1 := dA * b1 - m1
  set s2 := dA * b2 - m2
  set s3 := dA * b3 - m3
  have hS : ∀ u v : ℝ, 0 ≤ s1 * u ^ 2 + 2 * s2 * u * v + s3 * v ^ 2 := by
    intro u v
    have h := hQ (-((a3*c1 - a2*c3)*u + (a3*c2 - a2*c4)*v)) (-((a1*c3 - a2*c1)*u + (a1*c4 - a2*c2)*v))
      (dA * u) (dA * v)
    have e : a1*(-((a3*c1 - a2*c3)*u + (a3*c2 - a2*c4)*v))^2 +
        2*a2*(-((a3*c1 - a2*c3)*u + (a3*c2 - a2*c4)*v))*(-((a1*c3 - a2*c1)*u + (a1*c4 - a2*c2)*v)) +
        a3*(-((a1*c3 - a2*c1)*u + (a1*c4 - a2*c2)*v))^2 + b1*(dA*u)^2 + 2*b2*(dA*u)*(dA*v) +
        b3*(dA*v)^2 + 2*(c1*(-((a3*c1 - a2*c3)*u + (a3*c2 - a2*c4)*v))*(dA*u) +
        c2*(-((a3*c1 - a2*c3)*u + (a3*c2 - a2*c4)*v))*(dA*v) +
        c3*(-((a1*c3 - a2*c1)*u + (a1*c4 - a2*c2)*v))*(dA*u) +
        c4*(-((a1*c3 - a2*c1)*u + (a1*c4 - a2*c2)*v))*(dA*v)) =
        dA * (s1 * u ^ 2 + 2 * s2 * u * v + s3 * v ^ 2) := by
      simp only [s1, s2, s3, m1, m2, m3, dA]; ring
    rw [e] at h
    exact (mul_nonneg_iff_of_pos_left hA).mp h
  have hAq : ∀ u v : ℝ, 0 ≤ a1 * u ^ 2 + 2 * a2 * u * v + a3 * v ^ 2 := by
    intro u v; have := hQ u v 0 0; nlinarith
  have hM : ∀ u v : ℝ, 0 ≤ m1 * u ^ 2 + 2 * m2 * u * v + m3 * v ^ 2 := by
    intro u v
    have := hAq (c3 * u + c4 * v) (-(c1 * u + c2 * v))
    have e : a1 * (c3 * u + c4 * v) ^ 2 + 2 * a2 * (c3 * u + c4 * v) * (-(c1 * u + c2 * v)) +
      a3 * (-(c1 * u + c2 * v)) ^ 2 = m1 * u ^ 2 + 2 * m2 * u * v + m3 * v ^ 2 := by
      simp only [m1, m2, m3]; ring
    linarith
  obtain ⟨hs1, hs3, hs⟩ := g64n_psd2 s1 s2 s3 hS
  obtain ⟨hm1, hm3, hm⟩ := g64n_psd2 m1 m2 m3 hM
  obtain ⟨hT, hT2⟩ := g64n_mink2 s1 s2 s3 m1 m2 m3 hs1 hs3 hs hm1 hm3 hm
  have i1 : s1 * s3 - s2 ^ 2 = dA * dG := by
    simp only [s1, s2, s3, m1, m2, m3, dA, dG, g64n_dG]; ring
  have i2 : m1 * m3 - m2 ^ 2 = dA * (c1 * c4 - c2 * c3) ^ 2 := by
    simp only [m1, m2, m3, dA]; ring
  have i3 : s1 * m3 + s3 * m1 - 2 * s2 * m2 = dA * X := by
    simp only [s1, s2, s3, m1, m2, m3, dA, X, dG, g64n_dG]; ring
  rw [i1, i2, i3] at hT2
  rw [i3] at hT
  have hs' : 0 ≤ dA * dG := by rw [← i1]; linarith
  clear_value dG X dA m1 m2 m3 s1 s2 s3
  have hdG : 0 ≤ dG := by
    have : 0 ≤ dA * dG := hs'
    exact (mul_nonneg_iff_of_pos_left hA).mp this
  refine ⟨hdG, (mul_nonneg_iff_of_pos_left hA).mp hT, ?_⟩
  have e1 : 4 * (dA * dG * (dA * (c1 * c4 - c2 * c3) ^ 2)) = dA ^ 2 * (4 * dG * (c1 * c4 - c2 * c3) ^ 2) := by ring
  have e2 : (dA * X) ^ 2 = dA ^ 2 * X ^ 2 := by ring
  rw [e1, e2] at hT2
  exact le_of_mul_le_mul_left hT2 (by positivity)

theorem g64n_lim (f : ℝ → ℝ) (hf : Continuous f) (h : ∀ ε : ℝ, 0 < ε → 0 ≤ f ε) : 0 ≤ f 0 := by
  have ht : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds (f 0)) :=
    (hf.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall (fun ε hε => h ε hε))

theorem g64n_coreAll (a1 a2 a3 b1 b2 b3 c1 c2 c3 c4 : ℝ)
    (hQ : ∀ x1 x2 y1 y2 : ℝ, 0 ≤ a1*x1^2 + 2*a2*x1*x2 + a3*x2^2 + b1*y1^2 + 2*b2*y1*y2 + b3*y2^2 +
      2*(c1*x1*y1 + c2*x1*y2 + c3*x2*y1 + c4*x2*y2)) :
    let dG := g64n_dG a1 a2 a3 b1 b2 b3 c1 c2 c3 c4
    let X := (a1 * a3 - a2 ^ 2) * (b1 * b3 - b2 ^ 2) - dG - (c1 * c4 - c2 * c3) ^ 2
    0 ≤ dG ∧ 0 ≤ X ∧ 4 * dG * (c1 * c4 - c2 * c3) ^ 2 ≤ X ^ 2 ∧
      0 ≤ a1 * a3 - a2 ^ 2 ∧ 0 ≤ b1 * b3 - b2 ^ 2 := by
  intro dG X
  obtain ⟨ha1, ha3, ha⟩ := g64n_psd2 a1 a2 a3 (fun u v => by have := hQ u v 0 0; nlinarith)
  obtain ⟨hb1, hb3, hb⟩ := g64n_psd2 b1 b2 b3 (fun u v => by have := hQ 0 0 u v; nlinarith)
  have hε : ∀ ε : ℝ, 0 < ε → _ := fun ε hε => g64n_corePD (a1 + ε) a2 (a3 + ε) (b1 + ε) b2 (b3 + ε)
    c1 c2 c3 c4 (fun x1 x2 y1 y2 => by
      have := hQ x1 x2 y1 y2
      nlinarith [sq_nonneg x1, sq_nonneg x2, sq_nonneg y1, sq_nonneg y2])
    (by nlinarith)
  have c1' : Continuous (fun ε : ℝ => g64n_dG (a1 + ε) a2 (a3 + ε) (b1 + ε) b2 (b3 + ε) c1 c2 c3 c4) := by
    unfold g64n_dG; fun_prop
  refine ⟨?_, ?_, ?_, by nlinarith, by nlinarith⟩
  · have := g64n_lim _ c1' (fun ε h => (hε ε h).1)
    simpa using this
  · have := g64n_lim (fun ε : ℝ => ((a1 + ε) * (a3 + ε) - a2 ^ 2) * ((b1 + ε) * (b3 + ε) - b2 ^ 2) -
      g64n_dG (a1 + ε) a2 (a3 + ε) (b1 + ε) b2 (b3 + ε) c1 c2 c3 c4 - (c1 * c4 - c2 * c3) ^ 2)
      (by fun_prop) (fun ε h => (hε ε h).2.1)
    simp only [add_zero] at this
    exact this
  · have := g64n_lim (fun ε : ℝ => (((a1 + ε) * (a3 + ε) - a2 ^ 2) * ((b1 + ε) * (b3 + ε) - b2 ^ 2) -
      g64n_dG (a1 + ε) a2 (a3 + ε) (b1 + ε) b2 (b3 + ε) c1 c2 c3 c4 - (c1 * c4 - c2 * c3) ^ 2) ^ 2 -
      4 * g64n_dG (a1 + ε) a2 (a3 + ε) (b1 + ε) b2 (b3 + ε) c1 c2 c3 c4 * (c1 * c4 - c2 * c3) ^ 2)
      (by fun_prop) (fun ε h => by have := (hε ε h).2.2; linarith)
    simp only [add_zero] at this
    linarith

theorem g64n_final (dA dB dC dG : ℝ) (hA : 0 ≤ dA) (hB : 0 ≤ dB) (hG : 0 ≤ dG)
    (hX : 0 ≤ dA * dB - dG - dC ^ 2) (hX2 : 4 * dG * dC ^ 2 ≤ (dA * dB - dG - dC ^ 2) ^ 2) :
    let u := (dA + dB) / 2
    let t := u - dC
    (Real.sqrt u - Real.sqrt (u - Real.sqrt dG)) ^ 2 ≤ t - Real.sqrt (t ^ 2 - dG) := by
  intro u t
  set D := Real.sqrt dG with hD
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hD2 : D ^ 2 = dG := Real.sq_sqrt hG
  have h2 : 2 * D * |dC| ≤ dA * dB - dG - dC ^ 2 := by
    have : (2 * D * |dC|) ^ 2 ≤ (dA * dB - dG - dC ^ 2) ^ 2 := by
      have : (2 * D * |dC|) ^ 2 = 4 * D ^ 2 * |dC| ^ 2 := by ring
      rw [this, hD2, sq_abs]; exact hX2
    by_contra hc; have hc := not_le.mp hc; nlinarith [abs_nonneg dC]
  have h3 : D + |dC| ≤ u := by
    have : (D + |dC|) ^ 2 ≤ u ^ 2 := by
      have : (D + |dC|) ^ 2 = D ^ 2 + |dC| ^ 2 + 2 * D * |dC| := by ring
      rw [this, hD2, sq_abs]; simp only [u]; nlinarith [sq_nonneg (dA - dB)]
    have hu : 0 ≤ u := by simp only [u]; linarith
    by_contra hc; have hc := not_le.mp hc; nlinarith [abs_nonneg dC]
  have hle := le_abs_self dC
  have hle' := neg_abs_le dC
  have htD : D ≤ t := by simp only [t]; linarith
  have huD : 0 ≤ u - D := by linarith
  have hu : 0 ≤ u := by linarith
  set s := Real.sqrt u with hs
  set w := Real.sqrt (u - D) with hw
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = u := Real.sq_sqrt hu
  have hw2 : w ^ 2 = u - D := Real.sq_sqrt huD
  have hr : 0 ≤ t ^ 2 - dG := by rw [← hD2]; nlinarith
  set r := Real.sqrt (t ^ 2 - dG) with hr'
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = t ^ 2 - D ^ 2 := by rw [Real.sq_sqrt hr, hD2]
  set t0 := 2 * u - D with ht0
  have htt0 : t ≤ t0 := by simp only [t, t0]; linarith
  -- r ≤ t, 2sw ≤ t0
  have hrt : r ≤ t := by
    by_contra hc; have hc := not_le.mp hc; nlinarith
  have hsw2 : (2 * s * w) ^ 2 = t0 ^ 2 - D ^ 2 := by
    have : (2 * s * w) ^ 2 = 4 * s ^ 2 * w ^ 2 := by ring
    rw [this, hs2, hw2]; simp only [t0]; ring
  have hswt0 : 2 * s * w ≤ t0 := by
    by_contra hc; have hc := not_le.mp hc; nlinarith
  have hgoal_eq : (s - w) ^ 2 = t0 - 2 * s * w := by
    have : (s - w) ^ 2 = s ^ 2 + w ^ 2 - 2 * s * w := by ring
    rw [this, hs2, hw2]; simp only [t0]; ring
  rw [hgoal_eq]
  -- need 2sw - r ≥ t0 - t
  have key : (2 * s * w - r) * (2 * s * w + r) = (t0 - t) * (t0 + t) := by
    have : (2 * s * w - r) * (2 * s * w + r) = (2 * s * w) ^ 2 - r ^ 2 := by ring
    rw [this, hsw2, hr2]; ring
  clear_value r t0 s w D t u
  rcases lt_or_eq_of_le (show 0 ≤ 2 * s * w + r by positivity) with hp | hp
  · have hsum : 2 * s * w + r ≤ t0 + t := by linarith
    have : (t0 - t) * (2 * s * w + r) ≤ (2 * s * w - r) * (2 * s * w + r) := by
      rw [key]; exact mul_le_mul_of_nonneg_left hsum (by linarith)
    have := le_of_mul_le_mul_right this hp
    linarith
  · have hsw : 0 ≤ 2 * s * w := by positivity
    have hr0' : r = 0 := by linarith
    have hsw0 : 2 * s * w = 0 := by linarith
    rw [hr0', hsw0] at key
    have ht0 : 0 ≤ t := by linarith
    have hm : 0 ≤ (t0 - t) * (2 * t) := mul_nonneg (by linarith) (by linarith)
    have hsq : (t0 - t) ^ 2 ≤ 0 := by
      have : (t0 - t) ^ 2 = (t0 - t) * (t0 + t) - (t0 - t) * (2 * t) := by ring
      rw [this, ← key]; linarith
    have : t0 - t = 0 := by
      have := sq_nonneg (t0 - t)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm hsq this)
    linarith

theorem g64n_det4 (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) :
    M.det = M (0,0) (0,0) * M (0,1) (0,1) * M (1,0) (1,0) * M (1,1) (1,1) - M (0,0) (0,0) * M (0,1) (0,1) * M (1,0) (1,1) * M (1,1) (1,0) - M (0,0) (0,0) * M (0,1) (1,0) * M (1,0) (0,1) * M (1,1) (1,1) + M (0,0) (0,0) * M (0,1) (1,0) * M (1,0) (1,1) * M (1,1) (0,1) + M (0,0) (0,0) * M (0,1) (1,1) * M (1,0) (0,1) * M (1,1) (1,0) - M (0,0) (0,0) * M (0,1) (1,1) * M (1,0) (1,0) * M (1,1) (0,1) - M (0,0) (0,1) * M (0,1) (0,0) * M (1,0) (1,0) * M (1,1) (1,1) + M (0,0) (0,1) * M (0,1) (0,0) * M (1,0) (1,1) * M (1,1) (1,0) + M (0,0) (0,1) * M (0,1) (1,0) * M (1,0) (0,0) * M (1,1) (1,1) - M (0,0) (0,1) * M (0,1) (1,0) * M (1,0) (1,1) * M (1,1) (0,0) - M (0,0) (0,1) * M (0,1) (1,1) * M (1,0) (0,0) * M (1,1) (1,0) + M (0,0) (0,1) * M (0,1) (1,1) * M (1,0) (1,0) * M (1,1) (0,0) + M (0,0) (1,0) * M (0,1) (0,0) * M (1,0) (0,1) * M (1,1) (1,1) - M (0,0) (1,0) * M (0,1) (0,0) * M (1,0) (1,1) * M (1,1) (0,1) - M (0,0) (1,0) * M (0,1) (0,1) * M (1,0) (0,0) * M (1,1) (1,1) + M (0,0) (1,0) * M (0,1) (0,1) * M (1,0) (1,1) * M (1,1) (0,0) + M (0,0) (1,0) * M (0,1) (1,1) * M (1,0) (0,0) * M (1,1) (0,1) - M (0,0) (1,0) * M (0,1) (1,1) * M (1,0) (0,1) * M (1,1) (0,0) - M (0,0) (1,1) * M (0,1) (0,0) * M (1,0) (0,1) * M (1,1) (1,0) + M (0,0) (1,1) * M (0,1) (0,0) * M (1,0) (1,0) * M (1,1) (0,1) + M (0,0) (1,1) * M (0,1) (0,1) * M (1,0) (0,0) * M (1,1) (1,0) - M (0,0) (1,1) * M (0,1) (0,1) * M (1,0) (1,0) * M (1,1) (0,0) - M (0,0) (1,1) * M (0,1) (1,0) * M (1,0) (0,0) * M (1,1) (0,1) + M (0,0) (1,1) * M (0,1) (1,0) * M (1,0) (0,1) * M (1,1) (0,0) := by
  rw [← Matrix.det_reindex_self finProdFinEquiv M]
  have e0 : finProdFinEquiv.symm (0 : Fin (2 * 2)) = ((0 : Fin 2), (0 : Fin 2)) := by decide
  have e1 : finProdFinEquiv.symm (1 : Fin (2 * 2)) = ((0 : Fin 2), (1 : Fin 2)) := by decide
  have e2 : finProdFinEquiv.symm (2 : Fin (2 * 2)) = ((1 : Fin 2), (0 : Fin 2)) := by decide
  have e3 : finProdFinEquiv.symm (3 : Fin (2 * 2)) = ((1 : Fin 2), (1 : Fin 2)) := by decide
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.reindex_apply,
    Fin.succAbove, e0, e1, e2, e3]
  ring

open scoped ComplexOrder in
theorem g64n_Q (gamma : Cov 2)
    (hgamma : physicalCovariance gamma (interleavedSymplecticForm 2)) (x1 x2 y1 y2 : ℝ) :
    0 ≤ gamma (0,0) (0,0) * x1^2 + 2 * gamma (0,0) (0,1) * x1 * x2 + gamma (0,1) (0,1) * x2^2 +
      gamma (1,0) (1,0) * y1^2 + 2 * gamma (1,0) (1,1) * y1 * y2 + gamma (1,1) (1,1) * y2^2 +
      2 * (gamma (0,0) (1,0) * x1 * y1 + gamma (0,0) (1,1) * x1 * y2 + gamma (0,1) (1,0) * x2 * y1 +
        gamma (0,1) (1,1) * x2 * y2) := by
  obtain ⟨hT, hP⟩ := hgamma
  have hs : ∀ i j, gamma j i = gamma i j := fun i j => by
    have := congrFun (congrFun hT i) j; simpa [Matrix.transpose_apply] using this
  let v : QuadratureIndex 2 → ℂ := fun k =>
    if k = (0,0) then (x1 : ℂ) else if k = (0,1) then (x2 : ℂ) else if k = (1,0) then (y1 : ℂ) else (y2 : ℂ)
  have h := hP.dotProduct_mulVec_nonneg v
  have h' := (Complex.nonneg_iff.mp h).1
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two, v] at h'
  simp [QAlgorithms.Papers.Independent.Dependency50.P10.complexify, interleavedSymplecticForm,
    Matrix.sub_apply, Complex.mul_re, Complex.mul_im] at h'
  rw [hs (0,1) (0,0), hs (1,1) (1,0), hs (1,0) (0,0), hs (1,1) (0,0), hs (1,0) (0,1), hs (1,1) (0,1)] at h' ⊢
  linarith [h']

theorem solution (gamma : Cov 2)
    (hgamma : physicalCovariance gamma (interleavedSymplecticForm 2)) :
    sourceF gamma ≥ sourceG gamma := by
  have hT := hgamma.1
  have hs : ∀ i j, gamma j i = gamma i j := fun i j => by
    have := congrFun (congrFun hT i) j; simpa [Matrix.transpose_apply] using this
  have hQ := g64n_Q gamma hgamma
  obtain ⟨hG, hX, hX2, hA, hB⟩ := g64n_coreAll _ _ _ _ _ _ _ _ _ _ hQ
  have hdet : gamma.det = g64n_dG (gamma (0,0) (0,0)) (gamma (0,0) (0,1)) (gamma (0,1) (0,1))
      (gamma (1,0) (1,0)) (gamma (1,0) (1,1)) (gamma (1,1) (1,1)) (gamma (0,0) (1,0))
      (gamma (0,0) (1,1)) (gamma (0,1) (1,0)) (gamma (0,1) (1,1)) := by
    rw [g64n_det4, g64n_dG]
    rw [hs (0,1) (0,0), hs (1,1) (1,0), hs (1,0) (0,0), hs (1,1) (0,0), hs (1,0) (0,1), hs (1,1) (0,1)]
    try ring
  have hdA : (modeCovarianceBlock gamma 0 0).det = gamma (0,0) (0,0) * gamma (0,1) (0,1) - gamma (0,0) (0,1) ^ 2 := by
    rw [Matrix.det_fin_two]; simp [modeCovarianceBlock]; rw [hs (0,1) (0,0)]; try ring
  have hdB : (modeCovarianceBlock gamma 1 1).det = gamma (1,0) (1,0) * gamma (1,1) (1,1) - gamma (1,0) (1,1) ^ 2 := by
    rw [Matrix.det_fin_two]; simp [modeCovarianceBlock]; rw [hs (1,1) (1,0)]; try ring
  have hdC : (modeCovarianceBlock gamma 0 1).det = gamma (0,0) (1,0) * gamma (0,1) (1,1) - gamma (0,0) (1,1) * gamma (0,1) (1,0) := by
    rw [Matrix.det_fin_two]; simp [modeCovarianceBlock]
  have := g64n_final _ _ _ _ hA hB hG hX hX2
  simp only [sourceF, sourceG, marginalAverage, ge_iff_le]
  rw [hdA, hdB, hdC, hdet]
  exact this

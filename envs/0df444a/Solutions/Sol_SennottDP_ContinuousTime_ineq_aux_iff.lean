-- Prove2me | solution 1 for SennottDP.ContinuousTime.ineq_aux_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T06:36:50.212592+00:00
-- url     : https://prove2.me/submissions/b7bb48fe-55a2-40f9-a795-a51531d9a3ce

import Mathlib
import Definitions.Def_SennottDP_ContinuousTime_CTMDC

set_option autoImplicit false

open SennottDP.ContinuousTime in
theorem solution {S Act : Type} [Countable S] (Ψ : CTMDC S Act) (hΨ : Ψ.IsValid)
    (tau B : ℝ) (hCTB : Ψ.CTB tau B) (e : S → Act) (he : ∀ i, e i ∈ Ψ.A i) (Z : ℝ) :
    (∀ w : S → ℝ, Ψ.Ineq1020 tau e Z w → Ψ.Ineq1015 e Z (fun i => tau * w i)) ∧
      (∀ z : S → ℝ, Ψ.Ineq1015 e Z z → Ψ.Ineq1020 tau e Z (fun i => z i / tau)) := by
  classical
  obtain ⟨htau, ⟨ε, hε, hε'⟩, -⟩ := hCTB
  have hP0 := hΨ.2.2.2
  have hν : ∀ i, 0 < Ψ.ν i (e i) := by
    intro i
    have h := hε' i (e i) (he i)
    unfold CTMDC.meanSojourn at h
    have h1 : 0 < 1 / Ψ.ν i (e i) := by linarith
    simpa using h1
  have hlt : ∀ i, tau * Ψ.ν i (e i) < 1 := by
    intro i
    have h := hε' i (e i) (he i)
    unfold CTMDC.meanSojourn at h
    have h2 : tau < 1 / Ψ.ν i (e i) := by linarith
    rw [lt_div_iff₀ (hν i)] at h2
    exact h2
  have hdecomp : ∀ i (w : S → ℝ) j,
      ((Ψ.aux tau).P i (e i) j).toReal * w j =
        tau * Ψ.ν i (e i) * ((Ψ.P i (e i) j).toReal * w j) +
          (if j = i then (1 - tau * Ψ.ν i (e i)) * w i else 0) := by
    intro i w j
    simp only [CTMDC.aux]
    by_cases hj : j = i
    · subst hj
      have h1 : 0 ≤ 1 - tau * Ψ.ν j (e j) := by linarith [hlt j]
      simp [hP0 j (e j) (he j), ENNReal.toReal_ofReal h1]
    · have h1 : 0 ≤ tau * Ψ.ν i (e i) := (mul_pos htau (hν i)).le
      simp [hj, ENNReal.toReal_mul, ENNReal.toReal_ofReal h1]
      ring
  have hsum : ∀ i (w : S → ℝ),
      Summable (fun j => ((Ψ.aux tau).P i (e i) j).toReal * w j) ↔
        Summable (fun j => (Ψ.P i (e i) j).toReal * w j) := by
    intro i w
    simp_rw [hdecomp i w]
    have hne : tau * Ψ.ν i (e i) ≠ 0 := (mul_pos htau (hν i)).ne'
    constructor
    · intro h
      have h2 := h.sub (hasSum_ite_eq i ((1 - tau * Ψ.ν i (e i)) * w i)).summable
      have h3 := h2.mul_left (tau * Ψ.ν i (e i))⁻¹
      refine h3.congr (fun j => ?_)
      simp only [add_sub_cancel_right]
      rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    · intro h
      exact (h.mul_left _).add (hasSum_ite_eq i _).summable
  have htsum : ∀ i (w : S → ℝ), Summable (fun j => (Ψ.P i (e i) j).toReal * w j) →
      ∑' j, ((Ψ.aux tau).P i (e i) j).toReal * w j =
        tau * Ψ.ν i (e i) * ∑' j, (Ψ.P i (e i) j).toReal * w j +
          (1 - tau * Ψ.ν i (e i)) * w i := by
    intro i w h
    simp_rw [hdecomp i w]
    rw [Summable.tsum_add (h.mul_left _) (hasSum_ite_eq i _).summable, tsum_mul_left,
      tsum_ite_eq]
  refine ⟨fun w hw i => ?_, fun z hz i => ?_⟩
  · obtain ⟨hs, hineq⟩ := hw i
    have hs' := (hsum i w).1 hs
    rw [htsum i w hs'] at hineq
    have hS : ∑' j, (Ψ.P i (e i) j).toReal * (tau * w j) =
        tau * ∑' j, (Ψ.P i (e i) j).toReal * w j := by
      rw [← tsum_mul_left]
      congr 1
      ext j
      ring
    refine ⟨(hs'.mul_left tau).congr (fun j => by ring), ?_⟩
    rw [hS]
    simp only [CTMDC.aux] at hineq
    unfold CTMDC.meanSojourn
    have hne : Ψ.ν i (e i) ≠ 0 := (hν i).ne'
    set ν := Ψ.ν i (e i)
    set Sw := ∑' j, (Ψ.P i (e i) j).toReal * w j
    have key : Ψ.G i (e i) * ν + Ψ.g i (e i) + tau * ν * Sw - Z - tau * ν * w i ≤ 0 := by
      linarith
    have heq : Z * (1 / ν) + tau * w i -
        (Ψ.G i (e i) + Ψ.g i (e i) * (1 / ν) + tau * Sw) =
        -(1 / ν) * (Ψ.G i (e i) * ν + Ψ.g i (e i) + tau * ν * Sw - Z - tau * ν * w i) := by
      field_simp
      ring
    have hpos : 0 ≤ -(1 / ν) * (Ψ.G i (e i) * ν + Ψ.g i (e i) + tau * ν * Sw - Z -
        tau * ν * w i) := by
      have : 0 < 1 / ν := one_div_pos.mpr (hν i)
      nlinarith
    linarith
  · obtain ⟨hs, hineq⟩ := hz i
    have hs' : Summable (fun j => (Ψ.P i (e i) j).toReal * (z j / tau)) :=
      (hs.mul_left tau⁻¹).congr (fun j => by ring)
    refine ⟨(hsum i _).2 hs', ?_⟩
    rw [htsum i _ hs']
    have hS : ∑' j, (Ψ.P i (e i) j).toReal * (z j / tau) =
        tau⁻¹ * ∑' j, (Ψ.P i (e i) j).toReal * z j := by
      rw [← tsum_mul_left]
      congr 1
      ext j
      ring
    rw [hS]
    simp only [CTMDC.aux]
    unfold CTMDC.meanSojourn at hineq
    have hne : Ψ.ν i (e i) ≠ 0 := (hν i).ne'
    have htne : tau ≠ 0 := htau.ne'
    set ν := Ψ.ν i (e i)
    set Sz := ∑' j, (Ψ.P i (e i) j).toReal * z j
    have key : 0 ≤ Z * (1 / ν) + z i - (Ψ.G i (e i) + Ψ.g i (e i) * (1 / ν) + Sz) := by
      linarith
    have heq : Z + z i / tau -
        (Ψ.G i (e i) * ν + Ψ.g i (e i) + (tau * ν * (tau⁻¹ * Sz) + (1 - tau * ν) * (z i / tau))) =
        ν * (Z * (1 / ν) + z i - (Ψ.G i (e i) + Ψ.g i (e i) * (1 / ν) + Sz)) := by
      field_simp
      ring
    have hpos : 0 ≤ ν * (Z * (1 / ν) + z i - (Ψ.G i (e i) + Ψ.g i (e i) * (1 / ν) + Sz)) :=
      mul_nonneg (hν i).le key
    linarith

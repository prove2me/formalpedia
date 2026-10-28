-- Prove2me | solution 1 for ProblemSpec.Equilibrium.eq_A_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:58:07.999709+00:00
-- url     : https://prove2.me/submissions/9afdf468-c3ff-450c-a545-70fc439ac380

import Mathlib
import Definitions.Def_ProblemSpec_Equilibrium_Model

open ProblemSpec.Equilibrium in
theorem solution (P : Params) (hP : P.Standing) (Sr Sg N : ℝ) (hSr : 0 ≤ Sr) (hSg : 0 ≤ Sg)
    (hN : 1 < N) (hII : rbar P N < Sr) :
    entryUtility P Sr Sg N = P.s ↔ N = N2closed P Sr := by
  obtain ⟨hA, hw, hμ, hc2, ⟨hν0, hν1⟩, ⟨hc10, hc1g⟩, ⟨hp0, hp1⟩, hs, hh, _⟩ := hP
  have hN0 : 0 < N := by linarith
  have hN1 : 0 < N - 1 := by linarith
  have hL0 : 0 < Real.log (1 / P.p) := Real.log_pos (one_lt_one_div hp0 hp1)
  have hL : 0 < L P := hL0
  have hbar : 0 < rbarArg P N := by
    unfold rbarArg
    exact mul_pos (mul_pos (mul_pos (div_pos hN1 (by positivity)) (div_pos hw hμ))
      (div_pos hA hc2)) (div_pos one_pos hL)
  have hlt : rgArg P N < rbarArg P N := by
    have e : rgArg P N = P.ν * rbarArg P N - P.cg / P.c2 * (1 / L P) := by
      unfold rgArg rbarArg; ring
    have h1 : 0 < P.cg / P.c2 * (1 / L P) :=
      mul_pos (div_pos (by linarith) hc2) (div_pos one_pos hL)
    rw [e]; nlinarith
  have hG : ¬ Guessing P N Sr := by
    rintro ⟨h1, h2⟩
    have : rg P N < rbar P N := by
      unfold rg rbar
      exact div_lt_div_of_pos_right (Real.log_lt_log h1 hlt) hL
    linarith
  have hrstar : rstar P N Sr = rbar P N := by
    unfold rstar
    rw [if_neg hG, if_neg (not_le.mpr hII)]
  have hpow : (1 / P.p) ^ (rbar P N) = rbarArg P N := by
    rw [Real.rpow_def_of_pos (by positivity : (0:ℝ) < 1 / P.p)]
    have : Real.log (1 / P.p) * rbar P N = Real.log (rbarArg P N) := by
      unfold rbar L
      field_simp
    rw [this, Real.exp_log hbar]
  have hhS : 0 < P.h Sg := hh Sg hSg
  have hM : 0 < mstar P Sg N := by
    unfold mstar
    exact div_pos (mul_pos hA hN1) (mul_pos (by positivity) hhS)
  have hhm : P.h Sg * mstar P Sg N = P.A * (N - 1) / N ^ 2 := by
    unfold mstar
    field_simp
  have hX : 0 < X P := by unfold X; exact div_pos hw (mul_pos hμ hL)
  have hc2b : P.c2 * rbarArg P N = P.A * (N - 1) * X P / N ^ 2 := by
    unfold rbarArg X
    field_simp
  have hEU : entryUtility P Sr Sg N =
      P.A / N - P.c1 * Sr - P.A * (N - 1) * (X P + 1) / N ^ 2 := by
    unfold entryUtility payoff winProb cost
    rw [hrstar, max_eq_right (by linarith : rbar P N - Sr ≤ 0), hpow, hhm, hc2b]
    set E := Real.exp (quality P Sr (rbar P N) / P.μ)
    set M := mstar P Sg N
    have hE : 0 < E := Real.exp_pos _
    have hME : 0 < M * E := mul_pos hM hE
    have hden : M * E + (N - 1) * M * E = N * (M * E) := by ring
    have hwin : M * E / (M * E + (N - 1) * M * E) = 1 / N := by
      rw [hden, eq_div_iff hN0.ne', div_mul_eq_mul_div, div_eq_iff (by positivity)]
      ring
    rw [hwin]
    field_simp
    ring
  have hYp : 0 < Y P Sr := by
    unfold Y
    exact div_pos (by nlinarith) hA
  have hid : P.A / N - P.c1 * Sr - P.A * (N - 1) * (X P + 1) / N ^ 2 - P.s =
      -(P.A / N ^ 2) * (Y P Sr * N ^ 2 + X P * N - (X P + 1)) := by
    unfold Y
    field_simp
    ring
  have hAN : -(P.A / N ^ 2) ≠ 0 := neg_ne_zero.mpr (by positivity)
  have hquad : entryUtility P Sr Sg N = P.s ↔ Y P Sr * N ^ 2 + X P * N - (X P + 1) = 0 := by
    rw [hEU]
    constructor
    · intro h
      rw [h, sub_self] at hid
      exact (mul_eq_zero.mp hid.symm).resolve_left hAN
    · intro h
      rw [h, mul_zero] at hid
      linarith
  rw [hquad]
  set Yv := Y P Sr
  set Xv := X P
  have hD : 0 ≤ 4 * Yv * (Xv + 1) + Xv ^ 2 := by positivity
  unfold N2closed
  rw [← show Yv = Y P Sr from rfl, ← show Xv = X P from rfl]
  constructor
  · intro hq
    have hsq : (2 * Yv * N + Xv) ^ 2 = 4 * Yv * (Xv + 1) + Xv ^ 2 := by
      linear_combination (4 * Yv) * hq
    have hs' : Real.sqrt (4 * Yv * (Xv + 1) + Xv ^ 2) = 2 * Yv * N + Xv := by
      rw [← hsq]; exact Real.sqrt_sq (by positivity)
    rw [hs', eq_div_iff (by positivity)]
    ring
  · intro hNe
    have e : 2 * Yv * N + Xv = Real.sqrt (4 * Yv * (Xv + 1) + Xv ^ 2) := by
      rw [hNe]; field_simp; ring
    have hs2 := Real.sq_sqrt hD
    have h4 : 4 * Yv * (Yv * N ^ 2 + Xv * N - (Xv + 1)) = 0 := by
      linear_combination (2 * Yv * N + Xv + Real.sqrt (4 * Yv * (Xv + 1) + Xv ^ 2)) * e + hs2
    have h4' : 4 * Yv ≠ 0 := by positivity
    exact (mul_eq_zero.mp h4).resolve_left h4'

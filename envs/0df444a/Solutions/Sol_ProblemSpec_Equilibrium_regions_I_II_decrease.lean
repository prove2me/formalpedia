-- Prove2me | solution 1 for ProblemSpec.Equilibrium.regions_I_II_decrease
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:19:26.571485+00:00
-- url     : https://prove2.me/submissions/251ccc49-73db-48cc-b7be-622a52f26f97

import Mathlib
import Definitions.Def_ProblemSpec_Equilibrium_Model

open ProblemSpec.Equilibrium in
theorem solution (P : Params) (hP : P.Standing) :
    StrictAntiOn (N1closed P) (Set.Ici 0) ∧
      ∀ Sr : ℝ, 0 ≤ Sr →
        HasDerivAt (N2closed P)
            (-((-(X P) * Real.sqrt (X P ^ 2 + 4 * X P * Y P Sr + 4 * Y P Sr) + X P ^ 2
                  + 2 * X P * Y P Sr + 2 * Y P Sr) /
                (2 * Y P Sr ^ 2 * Real.sqrt (X P ^ 2 + 4 * X P * Y P Sr + 4 * Y P Sr)))
              * (P.c1 / P.A)) Sr ∧
          -((-(X P) * Real.sqrt (X P ^ 2 + 4 * X P * Y P Sr + 4 * Y P Sr) + X P ^ 2
                + 2 * X P * Y P Sr + 2 * Y P Sr) /
              (2 * Y P Sr ^ 2 * Real.sqrt (X P ^ 2 + 4 * X P * Y P Sr + 4 * Y P Sr)))
            * (P.c1 / P.A) ≤ 0 := by
  obtain ⟨hA, hw, hμ, hc2, ⟨hν0, hν1⟩, ⟨hc10, hc1g⟩, ⟨hp0, hp1⟩, hs, -, -⟩ := hP
  have hL : 0 < L P := by
    unfold L
    apply Real.log_pos
    rw [one_div, one_lt_inv₀ hp0]; exact hp1
  have hX : 0 < X P := by unfold X; exact div_pos hw (mul_pos hμ hL)
  have hYpos : ∀ Sr, 0 ≤ Sr → 0 < Y P Sr := by
    intro Sr hSr; unfold Y; positivity
  refine ⟨?_, fun Sr hSr => ?_⟩
  · intro a ha b hb hab
    have hp1' : 1 < 1 / P.p := by rw [one_div, one_lt_inv₀ hp0]; exact hp1
    have hpow : (1 / P.p) ^ a < (1 / P.p) ^ b := Real.rpow_lt_rpow_of_exponent_lt hp1' hab
    have ha0 : (0:ℝ) ≤ a := ha
    have hpa : 0 < (1 / P.p) ^ a := Real.rpow_pos_of_pos (by positivity) a
    have hden1 : 0 < P.s + P.c1 * a + P.c2 * (1 / P.p) ^ a := by positivity
    have hden2 : P.s + P.c1 * a + P.c2 * (1 / P.p) ^ a < P.s + P.c1 * b + P.c2 * (1 / P.p) ^ b := by
      have := mul_lt_mul_of_pos_left hpow hc2
      have : P.c1 * a ≤ P.c1 * b := mul_le_mul_of_nonneg_left hab.le hc10
      linarith
    unfold N1closed
    have hden2pos : 0 < P.s + P.c1 * b + P.c2 * (1 / P.p) ^ b := by linarith
    apply Real.sqrt_lt_sqrt (div_nonneg hA.le hden2pos.le)
    exact div_lt_div_of_pos_left hA hden1 hden2
  · have hY := hYpos Sr hSr
    set x := X P with hxdef
    set y := Y P Sr with hydef
    set D := Real.sqrt (x ^ 2 + 4 * x * y + 4 * y) with hDdef
    have harg : 0 < x ^ 2 + 4 * x * y + 4 * y := by positivity
    have hD : 0 < D := Real.sqrt_pos.mpr harg
    have hD2 : D ^ 2 = x ^ 2 + 4 * x * y + 4 * y := Real.sq_sqrt harg.le
    refine ⟨?_, ?_⟩
    · have hYd : HasDerivAt (Y P) (P.c1 / P.A) Sr := by
        have := (((hasDerivAt_id Sr).const_mul P.c1).const_add P.s).div_const P.A
        rw [show Y P = fun t => (P.s + P.c1 * t) / P.A from rfl]
        simpa using this
      have hargd : HasDerivAt (fun t => 4 * Y P t * (x + 1) + x ^ 2)
          (4 * (P.c1 / P.A) * (x + 1)) Sr :=
        ((hYd.const_mul 4).mul_const (x + 1)).add_const _
      have hargne : 4 * Y P Sr * (x + 1) + x ^ 2 ≠ 0 := by
        rw [← hydef]; nlinarith
      have hsq := hargd.sqrt hargne
      have hnum := hsq.sub_const x
      have hden : HasDerivAt (fun t => 2 * Y P t) (2 * (P.c1 / P.A)) Sr := hYd.const_mul 2
      have hdenne : 2 * Y P Sr ≠ 0 := by rw [← hydef]; positivity
      have hdiv := hnum.div hden hdenne
      have heq : 4 * Y P Sr * (x + 1) + x ^ 2 = x ^ 2 + 4 * x * y + 4 * y := by rw [← hydef]; ring
      refine hdiv.congr_deriv ?_
      rw [heq, ← hDdef, ← hydef]
      field_simp
      linear_combination (-2 * P.c1) * hD2
    · have hnum : 0 ≤ -x * D + x ^ 2 + 2 * x * y + 2 * y := by
        have h1 : (x ^ 2 + 2 * x * y + 2 * y) ^ 2 - (x * D) ^ 2 = 4 * y ^ 2 * (x + 1) ^ 2 := by
          rw [mul_pow, hD2]; ring
        have h2 : 0 ≤ x * D := by positivity
        nlinarith [sq_nonneg (y * (x + 1))]
      have : 0 ≤ (-x * D + x ^ 2 + 2 * x * y + 2 * y) / (2 * y ^ 2 * D) := by positivity
      have hc : 0 ≤ P.c1 / P.A := by positivity
      nlinarith

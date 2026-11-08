-- Prove2me | solution 1 for ReviewProvision.eq_25_26
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:32:56.872113+00:00
-- url     : https://prove2.me/submissions/3e4bd4be-4122-4816-aa58-3467cba12e52

import Mathlib
import Definitions.Def_ReviewProvision_IsOptimal
import Definitions.Def_ReviewProvision_closedForms
import Definitions.Def_ReviewProvision_truncatedMoments

open MeasureTheory ProbabilityTheory

open ReviewProvision in
theorem solution (p : Params) {N : ℕ} (w : Fin N → ℝ) (hw : ∀ l, 0 ≤ w l) (l n : Fin N) :
    HasDerivAt (fun x => sigmaSqF p (Function.update w n x) l) (dSigmaSqF p w l n) (w n) ∧
    0 < dSigmaSqF p w l n := by
  have hE := p.eta_pos
  have hτ := p.tau_pos
  set R : ℝ := ∑ k ∈ Finset.univ.erase n, p.eta * w k / (p.eta + w k) with hR
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun k _ =>
    div_nonneg (mul_nonneg hE.le (hw k)) (by linarith [hw k])
  have hT' : ∀ x, T p (Function.update w n x) = p.eta * x / (p.eta + x) + R := by
    intro x
    unfold T
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ n), Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  have hTw : T p w = p.eta * w n / (p.eta + w n) + R := by
    have := hT' (w n)
    rwa [Function.update_eq_self] at this
  have hwn := hw n
  have hEw : 0 < p.eta + w n := by linarith
  have hT0 : 0 ≤ T p w := by
    rw [hTw]; exact add_nonneg (div_nonneg (mul_nonneg hE.le hwn) hEw.le) hR0
  have hU0 : 0 < p.tau + (p.eta * w n / (p.eta + w n) + R) := by rw [← hTw]; linarith
  -- derivative of the single summand
  have hx := hasDerivAt_id' (w n)
  have G : HasDerivAt (fun x => p.eta * x / (p.eta + x)) (p.eta ^ 2 / (p.eta + w n) ^ 2) (w n) := by
    have := (hx.const_mul p.eta).div (hx.const_add p.eta) hEw.ne'
    refine this.congr_deriv ?_
    try simp only [Pi.add_apply, Pi.mul_apply]
    try dsimp only
    field_simp <;> ring
  have hU := (G.add_const R).const_add p.tau
  by_cases hln : l = n
  · subst hln
    have hfun : (fun x => sigmaSqF p (Function.update w l x) l) = fun x =>
        (x * (p.tau + (p.eta * x / (p.eta + x) + R)) * (p.tau * (p.eta + x) + p.eta * x) +
          2 * p.eta ^ 2 * x * (p.tau + (p.eta * x / (p.eta + x) + R)) +
          p.eta ^ 3 * (p.eta * x / (p.eta + x) + R)) /
        (p.tau * p.eta * (p.eta + x) ^ 2 * (p.tau + (p.eta * x / (p.eta + x) + R))) := by
      funext x
      simp only [sigmaSqF, hT' x, Function.update_self]
    have hV := ((hx.const_add p.eta).const_mul p.tau).add (hx.const_mul p.eta)
    have hNum := (((hx.mul hU).mul hV).add ((hx.const_mul (2 * p.eta ^ 2)).mul hU)).add
      ((G.add_const R).const_mul (p.eta ^ 3))
    have hDen := (((hx.const_add p.eta).pow 2).const_mul (p.tau * p.eta)).mul hU
    have hne : p.tau * p.eta * (p.eta + w l) ^ 2 * (p.tau + (p.eta * w l / (p.eta + w l) + R)) ≠ 0 :=
      by positivity
    have hQ := hNum.div hDen hne
    refine ⟨?_, ?_⟩
    · rw [hfun]
      refine hQ.congr_deriv ?_
      try simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply]
      try dsimp only
      unfold dSigmaSqF
      rw [if_pos rfl, hTw]
      field_simp
      ring
    · simp only [dSigmaSqF, if_pos rfl]
      have : 0 < (p.tau + T p w) * (p.eta + w l) + p.eta ^ 2 := by positivity
      positivity
  · have hfun : (fun x => sigmaSqF p (Function.update w n x) l) = fun x =>
        (w l * (p.tau + (p.eta * x / (p.eta + x) + R)) * (p.tau * (p.eta + w l) + p.eta * w l) +
          2 * p.eta ^ 2 * w l * (p.tau + (p.eta * x / (p.eta + x) + R)) +
          p.eta ^ 3 * (p.eta * x / (p.eta + x) + R)) /
        (p.tau * p.eta * (p.eta + w l) ^ 2 * (p.tau + (p.eta * x / (p.eta + x) + R))) := by
      funext x
      simp only [sigmaSqF, hT' x, Function.update_of_ne hln]
    have hwl := hw l
    have hEl : 0 < p.eta + w l := by linarith
    have hNum := (((hU.const_mul (w l)).mul_const (p.tau * (p.eta + w l) + p.eta * w l)).add
      (hU.const_mul (2 * p.eta ^ 2 * w l))).add ((G.add_const R).const_mul (p.eta ^ 3))
    have hDen := hU.const_mul (p.tau * p.eta * (p.eta + w l) ^ 2)
    have hne : p.tau * p.eta * (p.eta + w l) ^ 2 * (p.tau + (p.eta * w n / (p.eta + w n) + R)) ≠ 0 :=
      by positivity
    have hQ := hNum.div hDen hne
    refine ⟨?_, ?_⟩
    · rw [hfun]
      refine hQ.congr_deriv ?_
      try simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply]
      try dsimp only
      unfold dSigmaSqF
      rw [if_neg hln, hTw]
      field_simp
      ring
    · simp only [dSigmaSqF, if_neg hln]
      have : 0 < p.tau + T p w := by linarith
      positivity

-- Prove2me | solution 1 for QueueingFundamentals.Transient.mm11_transient
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T03:38:19.286923+00:00
-- url     : https://prove2.me/submissions/91cb4ed1-e1a6-4098-b987-2bcb26475f2f

import Mathlib
import Definitions.Def_QueueingFundamentals_Transient_forwardEquations

namespace MM11Aux

theorem const_on_Ici (f : ℝ → ℝ) (hf : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt f 0 (Set.Ici (0 : ℝ)) t)
    (t : ℝ) (ht : 0 ≤ t) : f t = f 0 := by
  have hc : ContinuousOn f (Set.Icc 0 t) := fun x hx =>
    ((hf x hx.1).continuousWithinAt).mono Set.Icc_subset_Ici_self
  have := constant_of_has_deriv_right_zero hc (fun x hx =>
    (hf x hx.1).mono (Set.Ici_subset_Ici.mpr hx.1)) t ⟨ht, le_rfl⟩
  exact this

end MM11Aux

open QueueingFundamentals.Transient in
theorem solution (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (p : Fin 2 → ℝ → ℝ)
    (hsum : p 0 0 + p 1 0 = 1) :
    IsForwardSolution (mm11RHS lam mu) p ↔
      ∀ t : ℝ, 0 ≤ t →
        p 1 t = lam / (lam + mu) * (1 - Real.exp (-(lam + mu) * t))
            + p 1 0 * Real.exp (-(lam + mu) * t) ∧
        p 0 t = mu / (lam + mu) * (1 - Real.exp (-(lam + mu) * t))
            + p 0 0 * Real.exp (-(lam + mu) * t) := by
  have hlm : lam + mu ≠ 0 := by positivity
  constructor
  · intro h t ht
    have h0 : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt (p 0) (-lam * p 0 t + mu * p 1 t)
        (Set.Ici (0 : ℝ)) t := fun t ht => by
      simpa [mm11RHS] using h 0 t ht
    have h1 : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt (p 1) (-mu * p 1 t + lam * p 0 t)
        (Set.Ici (0 : ℝ)) t := fun t ht => by
      simpa [mm11RHS] using h 1 t ht
    have hs : ∀ t : ℝ, 0 ≤ t → p 0 t + p 1 t = 1 := by
      intro t ht
      have := MM11Aux.const_on_Ici (fun t => p 0 t + p 1 t) (fun x hx => by
        exact ((h0 x hx).add (h1 x hx)).congr_deriv (by ring)) t ht
      simpa [hsum] using this
    set c := lam / (lam + mu) with hc
    have hg := MM11Aux.const_on_Ici (fun t => Real.exp ((lam + mu) * t) * (p 1 t - c))
      (fun x hx => by
        have he : HasDerivWithinAt (fun t => Real.exp ((lam + mu) * t))
            (Real.exp ((lam + mu) * x) * (lam + mu)) (Set.Ici (0 : ℝ)) x := by
          have := ((hasDerivAt_id x).const_mul (lam + mu)).exp
          simpa using this.hasDerivWithinAt
        refine (he.mul ((h1 x hx).sub_const c)).congr_deriv ?_
        have hp0 : p 0 x = 1 - p 1 x := by linarith [hs x hx]
        have hcl : c * (lam + mu) = lam := by rw [hc]; field_simp
        rw [hp0]
        linear_combination (-(Real.exp ((lam + mu) * x))) * hcl) t ht
    simp only [mul_zero, Real.exp_zero, one_mul] at hg
    have hEE : Real.exp (-(lam + mu) * t) * Real.exp ((lam + mu) * t) = 1 := by
      have h00 : -(lam + mu) * t + (lam + mu) * t = 0 := by ring
      rw [← Real.exp_add, h00, Real.exp_zero]
    have hp1 : p 1 t = c * (1 - Real.exp (-(lam + mu) * t)) + p 1 0 * Real.exp (-(lam + mu) * t) := by
      linear_combination Real.exp (-(lam + mu) * t) * hg - (p 1 t - c) * hEE
    refine ⟨hp1, ?_⟩
    have := hs t ht
    have hc' : mu / (lam + mu) = 1 - c := by rw [hc]; field_simp; ring
    rw [hc']
    linear_combination this - hp1 - Real.exp (-(lam + mu) * t) * hsum
  · intro h n t ht
    set E : ℝ → ℝ := fun t => Real.exp (-(lam + mu) * t) with hE
    have hEd : ∀ x, HasDerivAt E (E x * (-(lam + mu))) x := fun x => by
      have := ((hasDerivAt_id x).const_mul (-(lam + mu))).exp
      simpa [hE] using this
    have key : ∀ (a b : ℝ) (k : Fin 2), (∀ s, 0 ≤ s → p k s = a * (1 - E s) + b * E s) →
        HasDerivWithinAt (p k) ((a - b) * (lam + mu) * E t) (Set.Ici (0 : ℝ)) t := by
      intro a b k hk
      have hf : HasDerivAt (fun s => a * (1 - E s) + b * E s)
          ((a - b) * (lam + mu) * E t) t := by
        exact (((hEd t).const_sub 1 |>.const_mul a).add ((hEd t).const_mul b)).congr_deriv
          (by ring)
      exact hf.hasDerivWithinAt.congr (fun s hs => hk s hs) (hk t ht)
    have hp1 : ∀ s, 0 ≤ s → p 1 s = lam / (lam + mu) * (1 - E s) + p 1 0 * E s :=
      fun s hs => (h s hs).1
    have hp0 : ∀ s, 0 ≤ s → p 0 s = mu / (lam + mu) * (1 - E s) + p 0 0 * E s :=
      fun s hs => (h s hs).2
    have hb : p 0 0 = 1 - p 1 0 := by linarith
    obtain rfl | rfl : n = 0 ∨ n = 1 := by fin_cases n <;> simp
    · refine (key _ _ 0 hp0).congr_deriv ?_
      rw [show mm11RHS lam mu (fun m => p m t) 0 = -lam * p 0 t + mu * p 1 t from by
        simp [mm11RHS]]
      rw [hp0 t ht, hp1 t ht, hb]; field_simp; ring
    · refine (key _ _ 1 hp1).congr_deriv ?_
      rw [show mm11RHS lam mu (fun m => p m t) 1 = -mu * p 1 t + lam * p 0 t from by
        simp [mm11RHS]]
      rw [hp0 t ht, hp1 t ht, hb]; field_simp; ring

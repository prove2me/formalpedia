-- Prove2me | solution 1 for Real.exp_decay_of_sq_mul_le_second_deriv
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-14T20:34:23.135886+00:00
-- url     : https://prove2.me/submissions/3cf1b2d7-4b52-4851-8b1a-f7e00015ec75

import Mathlib

open Set Filter Topology

namespace RH5

lemma mono_Ici (g g' : ℝ → ℝ) (a : ℝ) (hd : ∀ s ≥ a, HasDerivAt g (g' s) s)
    (hnn : ∀ s ≥ a, 0 ≤ g' s) : MonotoneOn g (Ici a) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici a)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => hnn x (interior_subset hx))


lemma anti_Ici (g g' : ℝ → ℝ) (a : ℝ) (hd : ∀ s ≥ a, HasDerivAt g (g' s) s)
    (hnp : ∀ s ≥ a, g' s ≤ 0) : AntitoneOn g (Ici a) := by
  have := mono_Ici (fun x => -g x) (fun x => -g' x) a (fun s hs => (hd s hs).neg)
    (fun s hs => by linarith [hnp s hs])
  intro x hx y hy hxy
  have := this hx hy hxy
  simp only at this
  linarith


/-- `f'' ≥ c² f`, `f ≥ 0`, `f → 0` ⇒ `f' ≤ 0` and `f(s) ≤ f(s₀) e^{-c(s - s₀)}`. -/
theorem ode_decay (f f1 f2 : ℝ → ℝ) (s0 c : ℝ) (hc : 0 < c)
    (hf : ∀ s ≥ s0, HasDerivAt f (f1 s) s) (hf1 : ∀ s ≥ s0, HasDerivAt f1 (f2 s) s)
    (hpos : ∀ s ≥ s0, 0 ≤ f s) (hlim : Tendsto f atTop (𝓝 0))
    (h2 : ∀ s ≥ s0, c ^ 2 * f s ≤ f2 s) :
    (∀ s ≥ s0, f1 s ≤ 0) ∧ ∀ s ≥ s0, f s ≤ f s0 * Real.exp (-(c * (s - s0))) := by
  have hf2 : ∀ s ≥ s0, 0 ≤ f2 s := fun s hs =>
    le_trans (mul_nonneg (sq_nonneg c) (hpos s hs)) (h2 s hs)
  have hm1 := mono_Ici f1 f2 s0 hf1 hf2
  have hneg : ∀ s ≥ s0, f1 s ≤ 0 := by
    intro a ha
    by_contra hpa
    push Not at hpa
    -- `f x ≥ f a + f1 a (x - a)`
    have hm := mono_Ici (fun x => f x - f1 a * x) (fun x => f1 x - f1 a) a
      (fun x hx => (hf x (ha.trans hx)).sub ((hasDerivAt_id x).const_mul (f1 a)) |>.congr_deriv
        (by simp))
      (fun x hx => by linarith [hm1 ha (show s0 ≤ x from ha.trans hx) hx])
    obtain ⟨N, hN⟩ := (eventually_atTop.1 (hlim.eventually (gt_mem_nhds zero_lt_one)))
    set x := max N (a + 2 / f1 a)
    have hpos2 : 0 < 2 / f1 a := by positivity
    have hxa : a ≤ x := le_trans (by linarith) (le_max_right N (a + 2 / f1 a))
    have h1 := hm (le_refl a) hxa hxa
    simp only at h1
    have h3 := hN x (le_max_left _ _)
    have h4 := hpos a ha
    have h5 : f1 a * (x - a) ≥ 2 := by
      have : x - a ≥ 2 / f1 a := by have := le_max_right N (a + 2 / f1 a); linarith
      calc f1 a * (x - a) ≥ f1 a * (2 / f1 a) := by gcongr
        _ = 2 := by field_simp
    nlinarith
  refine ⟨hneg, ?_⟩
  -- `w = f' + c f ≤ 0`
  have hw : ∀ s ≥ s0, f1 s + c * f s ≤ 0 := by
    intro a ha
    by_contra hpa
    push Not at hpa
    have hm := mono_Ici (fun x => Real.exp (-(c * x)) * (f1 x + c * f x))
      (fun x => Real.exp (-(c * x)) * (f2 x - c ^ 2 * f x)) a
      (fun x hx => by
        have hx0 : s0 ≤ x := ha.trans hx
        have e := ((hasDerivAt_id x).const_mul c).neg.exp.mul ((hf1 x hx0).add ((hf x hx0).const_mul c))
        refine e.congr_deriv ?_
        simp only [id, mul_one, Pi.neg_apply, Pi.add_apply, Pi.mul_apply]
        ring)
      (fun x hx => mul_nonneg (Real.exp_pos _).le (by linarith [h2 x (ha.trans hx)]))
    obtain ⟨N, hN⟩ := (eventually_atTop.1 (hlim.eventually
      (gt_mem_nhds (show 0 < (f1 a + c * f a) / c by positivity))))
    set x := max N a
    have hxa : a ≤ x := le_max_right _ _
    have h1 := hm (le_refl a) hxa hxa
    simp only at h1
    have hfx := hN x (le_max_left _ _)
    have hneg' := hneg x (ha.trans hxa)
    -- `exp(-cx) w(x) ≥ exp(-ca) w(a)` gives `w(x) ≥ w(a)`
    have hexp : Real.exp (-(c * a)) ≥ Real.exp (-(c * x)) := by
      apply Real.exp_le_exp.2; nlinarith
    have hwx : f1 x + c * f x ≥ f1 a + c * f a := by
      by_contra hlt
      push Not at hlt
      have : Real.exp (-(c * x)) * (f1 x + c * f x) < Real.exp (-(c * a)) * (f1 a + c * f a) := by
        calc Real.exp (-(c * x)) * (f1 x + c * f x) < Real.exp (-(c * x)) * (f1 a + c * f a) :=
              mul_lt_mul_of_pos_left hlt (Real.exp_pos _)
          _ ≤ Real.exp (-(c * a)) * (f1 a + c * f a) :=
              mul_le_mul_of_nonneg_right hexp hpa.le
      linarith
    have : c * f x < f1 a + c * f a := by
      have := (lt_div_iff₀ hc).1 hfx; linarith
    linarith
  -- `exp(c s) f s` is antitone
  have ha := anti_Ici (fun x => Real.exp (c * x) * f x)
    (fun x => Real.exp (c * x) * (f1 x + c * f x)) s0
    (fun x hx => by
      have e := ((hasDerivAt_id x).const_mul c).exp.mul (hf x hx)
      refine e.congr_deriv ?_
      simp only [id, mul_one, Pi.neg_apply, Pi.add_apply, Pi.mul_apply]
      ring)
    (fun x hx => mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (hw x hx))
  intro s hs
  have h := ha (le_refl s0) hs hs
  simp only at h
  have e : Real.exp (-(c * (s - s0))) = Real.exp (c * s0) / Real.exp (c * s) := by
    rw [← Real.exp_sub]; ring_nf
  rw [e, mul_div_assoc', le_div_iff₀ (Real.exp_pos _)]
  linarith

end RH5

open Real

open Filter Topology

theorem solution (f f1 f2 : ℝ → ℝ) (s0 c : ℝ) (hc : 0 < c)
    (hf : ∀ s ≥ s0, HasDerivAt f (f1 s) s) (hf1 : ∀ s ≥ s0, HasDerivAt f1 (f2 s) s)
    (hpos : ∀ s ≥ s0, 0 ≤ f s) (hlim : Tendsto f atTop (𝓝 0))
    (h2 : ∀ s ≥ s0, c ^ 2 * f s ≤ f2 s) :
    (∀ s ≥ s0, f1 s ≤ 0) ∧ ∀ s ≥ s0, f s ≤ f s0 * Real.exp (-(c * (s - s0))) :=
  RH5.ode_decay f f1 f2 s0 c hc hf hf1 hpos hlim h2

-- Prove2me | solution 1 for TokenFinance.Statics.eq_42
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T11:07:54.743554+00:00
-- url     : https://prove2.me/submissions/e1fe069a-7490-419e-b952-3ec586a9784d

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace TokenResearch
open TokenFinance.Debt
 def G (c θ t : ℝ) : ℝ := c/(c+t)*(2/(3*θ))*((θ-c)/2-t)^3-(θ-c)^3/(12*θ)
 def Dt (c θ t : ℝ) : ℝ := -(c/(c+t)^2)*(2/(3*θ))*((θ-c)/2-t)^3-2*c/((c+t)*θ)*((θ-c)/2-t)^2
 def Dc (c θ t : ℝ) : ℝ := 2*t/3*((θ-c)/2-t)^3/((c+t)^2*θ)+((θ-c)^2/(4*θ)-c*((θ-c)/2-t)^2/((c+t)*θ))
 def Dh (c θ t : ℝ) : ℝ := c/3*((θ-c)/2-t)^2*(2*θ+c+2*t)/((c+t)*θ^2)-(θ-c)^2*(2*θ+c)/(12*θ^2)
lemma deriv_t (c θ t : ℝ) (hct : c+t≠0) : HasDerivAt (G c θ) (Dt c θ t) t := by
  have h := ((((hasDerivAt_const t c).div ((hasDerivAt_id t).const_add c) hct).mul_const (2/(3*θ))).mul
    (((hasDerivAt_const t ((θ-c)/2)).sub (hasDerivAt_id t)).pow 3)).sub_const ((θ-c)^3/(12*θ))
  convert h using 1 <;> (try rfl) <;> (try dsimp [G,Dt]) <;> (try field_simp) <;> ring
lemma deriv_c (c θ t : ℝ) (hct : c+t≠0) : HasDerivAt (fun d => G d θ t) (Dc c θ t) c := by
  have h := ((((hasDerivAt_id c).div ((hasDerivAt_id c).add_const t) hct).mul_const (2/(3*θ))).mul
    ((((hasDerivAt_const c θ).sub (hasDerivAt_id c)).div_const 2).sub_const t |>.pow 3)).sub
      ((((hasDerivAt_const c θ).sub (hasDerivAt_id c)).pow 3).div_const (12*θ))
  convert h using 1 <;> (try rfl) <;> (try dsimp [G,Dc]) <;> (try field_simp) <;> ring
lemma deriv_h (c θ t : ℝ) (hθ : θ≠0) : HasDerivAt (fun T => G c T t) (Dh c θ t) θ := by
  have h := (((hasDerivAt_const θ (c/(c+t))).mul
      ((hasDerivAt_const θ 2).div ((hasDerivAt_id θ).const_mul 3) (by positivity : 3*θ≠0))).mul
      ((((hasDerivAt_id θ).sub_const c).div_const 2).sub_const t |>.pow 3)).sub
      ((((hasDerivAt_id θ).sub_const c).pow 3).div ((hasDerivAt_id θ).const_mul 12) (by positivity : 12*θ≠0))
  convert h using 1 <;> (try rfl) <;> (try dsimp [G,Dh]) <;> (try field_simp) <;> ring
lemma dt_neg (c θ t : ℝ) (hc : 0<c) (hθ : 0<θ) (ht : 0≤t) (hregion : t<(θ-c)/2) : Dt c θ t<0 := by
  have hct : 0<c+t := by linarith
  have hgap : 0<(θ-c)/2-t := by linarith
  have h1 : 0<c/(c+t)^2*(2/(3*θ))*((θ-c)/2-t)^3 := by positivity
  have h2 : 0<2*c/((c+t)*θ)*((θ-c)/2-t)^2 := by positivity
  dsimp [Dt]
  nlinarith only [h1,h2]
lemma dc_pos (c θ t : ℝ) (hc : 0<c) (ht : 0<t) (hregion : c+2*t<θ) : 0<Dc c θ t := by
  have hθ : 0<θ := by linarith
  have hct : 0<c+t := by linarith
  let u := θ-c-2*t
  have hu : 0<u := by dsimp [u];linarith
  have hid : Dc c θ t = t*(12*c^2*t+12*c^2*u+24*c*t^2+24*c*t*u+3*c*u^2+12*t^3+12*t^2*u+3*t*u^2+u^3)/(12*(c+t)^2*θ) := by
    dsimp [Dc,u]
    field_simp
    <;> ring
  rw [hid]
  positivity
lemma dh_neg (c θ t : ℝ) (hc : 0<c) (ht : 0<t) (hregion : c+2*t<θ) : Dh c θ t<0 := by
  have hθ : 0<θ := by linarith
  have hct : 0<c+t := by linarith
  let u := θ-c-2*t
  have hu : 0<u := by dsimp [u];linarith
  have hid : Dh c θ t = -(t*(12*c^2*t+12*c^2*u+28*c*t^2+36*c*t*u+9*c*u^2+16*t^3+24*t^2*u+12*t*u^2+2*u^3)/(12*(c+t)*θ^2)) := by
    dsimp [Dh,u]
    field_simp
    <;> ring
  rw [hid]
  apply neg_neg_of_pos
  positivity
end TokenResearch



theorem solution (c C0 θ t : ℝ) (hc : 0 < c) (hθ : 0 < θ) (ht : -c < t)
    (hregion : 0 ≤ t ∧ t < (θ - c) / 2) :
    HasDerivAt
        (fun s : ℝ => c / (c + s) * (2 / (3 * θ)) * ((θ - c) / 2 - s) ^ 3 -
          (θ - c) ^ 3 / (12 * θ) + C0)
        (-(c / (c + t) ^ 2) * (2 / (3 * θ)) * ((θ - c) / 2 - t) ^ 3 -
          2 * c / ((c + t) * θ) * ((θ - c) / 2 - t) ^ 2) t ∧
      (-(c / (c + t) ^ 2) * (2 / (3 * θ)) * ((θ - c) / 2 - t) ^ 3 -
        2 * c / ((c + t) * θ) * ((θ - c) / 2 - t) ^ 2) < 0 := by
  constructor
  · simpa [TokenResearch.G,TokenResearch.Dt] using (TokenResearch.deriv_t c θ t (by linarith)).add_const C0
  · exact TokenResearch.dt_neg c θ t hc hθ hregion.1 hregion.2



#print axioms solution

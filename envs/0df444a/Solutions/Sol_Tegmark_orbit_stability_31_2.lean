-- Prove2me | solution 2 for Tegmark.orbit_stability_31
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:46:27.34353+00:00
-- url     : https://prove2.me/submissions/84f47d10-a1ac-4b1c-9a78-468d4bd59550

import Mathlib
import Definitions.Def_Tegmark_sig
import Definitions.Def_Tegmark_phys
import Definitions.Def_Tegmark_ensemble
set_option autoImplicit false

open Tegmark

lemma uu_h1 (k L a x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => L ^ 2 / (2 * x ^ 2) + (-k * x ^ (2 - a)))
      (-(L ^ 2) / x ^ 3 + k * (a - 2) * x ^ (1 - a)) x := by
  have hx0 : x ≠ 0 := hx.ne'
  have h2 : HasDerivAt (fun x : ℝ => 2 * x ^ 2) (2 * (2 * x)) x := by
    simpa using ((hasDerivAt_pow 2 x).const_mul 2)
  have h3 : HasDerivAt (fun x : ℝ => L ^ 2 / (2 * x ^ 2))
      ((0 * (2 * x ^ 2) - L ^ 2 * (2 * (2 * x))) / (2 * x ^ 2) ^ 2) x :=
    (hasDerivAt_const x (L ^ 2)).div h2 (by positivity)
  have h4 : HasDerivAt (fun x : ℝ => x ^ (2 - a)) ((2 - a) * x ^ (2 - a - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx0)
  have h5 := h3.add (h4.const_mul (-k))
  refine h5.congr_deriv ?_
  have e : (2 - a - 1) = 1 - a := by ring
  rw [e]
  field_simp
  ring

lemma uu_h2 (k L a x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => -(L ^ 2) / x ^ 3 + k * (a - 2) * x ^ (1 - a))
      (3 * L ^ 2 / x ^ 4 + k * (a - 2) * (1 - a) * x ^ (-a)) x := by
  have hx0 : x ≠ 0 := hx.ne'
  have h2 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * x ^ 2) x := by
    simpa using (hasDerivAt_pow 3 x)
  have h3 : HasDerivAt (fun x : ℝ => -(L ^ 2) / x ^ 3)
      ((0 * x ^ 3 - (-(L ^ 2)) * (3 * x ^ 2)) / (x ^ 3) ^ 2) x :=
    (hasDerivAt_const x (-(L ^ 2))).div h2 (by positivity)
  have h4 : HasDerivAt (fun x : ℝ => x ^ (1 - a)) ((1 - a) * x ^ (1 - a - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx0)
  have h5 := h3.add (h4.const_mul (k * (a - 2)))
  refine h5.congr_deriv ?_
  have e : (1 - a - 1) = -a := by ring
  rw [e]
  field_simp
  ring

lemma uu_d1 (k L : ℝ) (n : ℕ) (r : ℝ) (hr : 0 < r) :
    deriv (effPot k L n) r = -(L ^ 2) / r ^ 3 + k * ((n : ℝ) - 2) * r ^ (1 - (n : ℝ)) := by
  have e : effPot k L n = fun x : ℝ => L ^ 2 / (2 * x ^ 2) + (-k * x ^ (2 - (n : ℝ))) := rfl
  rw [e]
  exact (uu_h1 k L (n : ℝ) r hr).deriv

lemma uu_d2 (k L : ℝ) (n : ℕ) (r : ℝ) (hr : 0 < r) :
    deriv (fun x => deriv (effPot k L n) x) r
      = 3 * L ^ 2 / r ^ 4 + k * ((n : ℝ) - 2) * (1 - (n : ℝ)) * r ^ (-(n : ℝ)) := by
  have hev : (fun x => deriv (effPot k L n) x) =ᶠ[nhds r]
      (fun x : ℝ => -(L ^ 2) / x ^ 3 + k * ((n : ℝ) - 2) * x ^ (1 - (n : ℝ))) :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds hr) (fun x hx => uu_d1 k L n x hx)
  rw [hev.deriv_eq]
  exact (uu_h2 k L (n : ℝ) r hr).deriv

theorem solution (n : ℕ) (_hn : 3 ≤ n) : HasStableOrbit n ↔ n = 3 := by
  constructor
  · rintro ⟨k, L, r, hk, hL, ⟨⟨hr, hc⟩, hs⟩⟩
    rw [uu_d1 k L n r hr] at hc
    rw [uu_d2 k L n r hr] at hs
    set a : ℝ := (n : ℝ) with ha
    have hP : 0 < r ^ (-a) := Real.rpow_pos_of_pos hr _
    have e : r ^ (1 - a) = r * r ^ (-a) := by
      rw [show (1 - a) = 1 + -a by ring, Real.rpow_add hr, Real.rpow_one]
    rw [e] at hc
    have key : k * (a - 2) * r ^ (-a) = L ^ 2 / r ^ 4 := by
      field_simp at hc ⊢
      nlinarith [hc]
    have h4 : 0 < L ^ 2 / r ^ 4 := by positivity
    have hs' : 3 * L ^ 2 / r ^ 4 + (1 - a) * (k * (a - 2) * r ^ (-a)) > 0 := by
      have : 3 * L ^ 2 / r ^ 4 + k * (a - 2) * (1 - a) * r ^ (-a)
          = 3 * L ^ 2 / r ^ 4 + (1 - a) * (k * (a - 2) * r ^ (-a)) := by ring
      linarith
    rw [key] at hs'
    have h4' : 3 * L ^ 2 / r ^ 4 = 3 * (L ^ 2 / r ^ 4) := by ring
    rw [h4'] at hs'
    have : a < 4 := by
      by_contra hcon
      rw [not_lt] at hcon
      nlinarith
    have : (n : ℝ) < 4 := this
    have : n < 4 := by exact_mod_cast this
    omega
  · rintro rfl
    refine ⟨1, 1, 1, one_pos, one_pos, ⟨⟨one_pos, ?_⟩, ?_⟩⟩
    · rw [uu_d1 1 1 3 1 one_pos]; norm_num
    · rw [uu_d2 1 1 3 1 one_pos]; norm_num

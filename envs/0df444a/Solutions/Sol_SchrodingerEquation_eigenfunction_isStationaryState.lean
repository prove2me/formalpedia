-- Prove2me | solution 1 for SchrodingerEquation.eigenfunction_isStationaryState
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:11:48.656306+00:00
-- url     : https://prove2.me/submissions/f2a0ca93-b271-48c5-81d0-89d8de130a4d

import Definitions.Def_SchrodingerEquation_infinite_well_model

open SchrodingerEquation

namespace Ag1Aux_SchStat

theorem hasDerivAt_sin_ofReal (a x : ℝ) :
    HasDerivAt (fun y : ℝ => ((Real.sin (a * y) : ℝ) : ℂ)) (((a * Real.cos (a * x)) : ℝ) : ℂ) x := by
  have h : HasDerivAt (fun y : ℝ => Real.sin (a * y)) (Real.cos (a * x) * a) x :=
    (Real.hasDerivAt_sin (a * x)).comp x ((hasDerivAt_id x).const_mul a |>.congr_deriv (by simp))
  have := h.ofReal_comp
  rw [mul_comm] at this
  exact this

theorem hasDerivAt_cos_ofReal (a b x : ℝ) :
    HasDerivAt (fun y : ℝ => (((b * Real.cos (a * y)) : ℝ) : ℂ))
      (((-(b * a * Real.sin (a * x))) : ℝ) : ℂ) x := by
  have h : HasDerivAt (fun y : ℝ => b * Real.cos (a * y)) (b * (-Real.sin (a * x) * a)) x :=
    ((Real.hasDerivAt_cos (a * x)).comp x ((hasDerivAt_id x).const_mul a |>.congr_deriv (by simp))).const_mul b
  have := h.ofReal_comp
  convert this using 2
  push_cast; ring

end Ag1Aux_SchStat

open Ag1Aux_SchStat

theorem solution (hbar m L : ℝ) (n : ℕ)
    (hbar_pos : 0 < hbar) (hm : 0 < m) (hL : 0 < L) (hn : 1 ≤ n) :
    IsStationaryState hbar m L (energyLevel hbar m L n) (eigenfunction L n) ∧
      ∃ x ∈ Set.Ioo 0 L, eigenfunction L n x ≠ 0 := by
  set a : ℝ := n * Real.pi / L with ha
  have hfun : eigenfunction L n = fun y : ℝ => ((Real.sin (a * y) : ℝ) : ℂ) := by
    funext y; simp only [eigenfunction, ha]; congr 2; ring
  have hd1 : deriv (eigenfunction L n) = fun y : ℝ => (((a * Real.cos (a * y)) : ℝ) : ℂ) := by
    funext y; rw [hfun, (hasDerivAt_sin_ofReal a y).deriv]
  have hd2 : ∀ y, deriv (deriv (eigenfunction L n)) y = ((-(a * a * Real.sin (a * y)) : ℝ) : ℂ) := by
    intro y; rw [hd1, (hasDerivAt_cos_ofReal a a y).deriv]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hfun]; fun_prop
  · intro x _; rw [hfun]; exact (hasDerivAt_sin_ofReal a x).differentiableAt
  · intro x _; rw [hd1]; exact (hasDerivAt_cos_ofReal a a x).differentiableAt
  · intro x _
    rw [hd2, hfun]
    simp only [energyLevel, ha]
    have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    push_cast
    field_simp <;> ring
  · simp [eigenfunction]
  · simp only [eigenfunction]
    have : (n : ℝ) * Real.pi * L / L = n * Real.pi := by field_simp
    rw [this, Real.sin_nat_mul_pi]; simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    refine ⟨L / (2 * n), ⟨by positivity, ?_⟩, ?_⟩
    · rw [div_lt_iff₀ (by positivity)]; nlinarith
    · simp only [eigenfunction]
      have : (n : ℝ) * Real.pi * (L / (2 * n)) / L = Real.pi / 2 := by field_simp
      rw [this, Real.sin_pi_div_two]; simp

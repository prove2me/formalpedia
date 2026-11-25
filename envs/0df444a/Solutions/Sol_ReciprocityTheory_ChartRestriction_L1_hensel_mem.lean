-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.hensel_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:02:55.935568+00:00
-- url     : https://prove2.me/submissions/f71462cd-16e2-44ce-b914-3f66816e6757

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurNewton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorHensel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kur_complete
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_newton_derivative_coeff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_newton_expansion
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_newton_lipschitz
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_newton_root
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_res_full
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_tch_mem_kur
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_tch_norm_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (P : Polynomial ℂ_[l]) (hK : ∀ i, P.coeff i ∈ MaximalUnramifiedExtension l) (hP : ∀ i, ‖P.coeff i‖ ≤ 1)
    (x : ℂ_[l]) (hx : ‖x‖ ≤ 1) (h0 : P.eval x = 0) (h1 : ‖P.derivative.eval x‖ = 1) : x ∈ MaximalUnramifiedExtension l := by
  have : CompleteSpace (MaximalUnramifiedExtension l) := kur_complete l
  obtain ⟨Q, hQ⟩ : ∃ Q : Polynomial (MaximalUnramifiedExtension l), Q.map (MaximalUnramifiedExtension l).subtype = P := by
    have : P ∈ Polynomial.lifts (MaximalUnramifiedExtension l).subtype := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro i
      exact ⟨⟨P.coeff i, hK i⟩, rfl⟩
    exact (Polynomial.mem_lifts P).mp this
  obtain ⟨ξ, hξ, hd⟩ := res_full l x hx
  have hξ1 : ‖ξ‖ ≤ 1 := tch_norm_le l hξ
  let a : MaximalUnramifiedExtension l := ⟨ξ, tch_mem_kur l hξ⟩
  have hev : ∀ b : MaximalUnramifiedExtension l, ((Q.eval b : MaximalUnramifiedExtension l) : ℂ_[l]) = P.eval (b : ℂ_[l]) := fun b => by
    rw [← hQ]
    exact (Polynomial.eval_map_apply (MaximalUnramifiedExtension l).subtype b).symm
  have hdev : ∀ b : MaximalUnramifiedExtension l, ((Q.derivative.eval b : MaximalUnramifiedExtension l) : ℂ_[l]) = P.derivative.eval (b : ℂ_[l]) :=
    fun b => by
      rw [← hQ, Polynomial.derivative_map]
      exact (Polynomial.eval_map_apply (MaximalUnramifiedExtension l).subtype b).symm
  have hQc : ∀ i, ‖Q.coeff i‖ ≤ 1 := fun i => by
    have := hP i
    rw [← hQ, Polynomial.coeff_map] at this
    exact this
  have e0 : ‖P.eval ξ‖ < 1 := by
    have := newton_lipschitz P hP ξ x hξ1 hx
    rw [h0, sub_zero, norm_sub_rev] at this
    exact lt_of_le_of_lt this hd
  have e1 : ‖P.derivative.eval ξ‖ = 1 := by
    have h2 := newton_lipschitz P.derivative (newton_derivative_coeff P hP) ξ x hξ1 hx
    rw [norm_sub_rev ξ x] at h2
    have h3 : ‖P.derivative.eval ξ - P.derivative.eval x‖ < ‖P.derivative.eval x‖ := by
      rw [h1]; exact lt_of_le_of_lt h2 hd
    have h4 : P.derivative.eval ξ = (P.derivative.eval ξ - P.derivative.eval x) + P.derivative.eval x := by
      ring
    rw [h4, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h3.ne, max_eq_right h3.le, h1]
  obtain ⟨x', hx'0, hx'd⟩ := newton_root Q hQc a hξ1
    (show ‖((Q.eval a : MaximalUnramifiedExtension l) : ℂ_[l])‖ < 1 by rw [hev]; exact e0)
    (show ‖((Q.derivative.eval a : MaximalUnramifiedExtension l) : ℂ_[l])‖ = 1 by rw [hdev]; exact e1)
  have hx'd' : ‖(x' : ℂ_[l]) - ξ‖ < 1 := by
    have h5 : ‖((x' - a : MaximalUnramifiedExtension l) : ℂ_[l])‖ ≤ ‖((Q.eval a : MaximalUnramifiedExtension l) : ℂ_[l])‖ := hx'd
    rw [hev] at h5
    exact lt_of_le_of_lt h5 e0
  have hP0 : P.eval (x' : ℂ_[l]) = 0 := by
    rw [← hev, hx'0]; rfl
  set y : ℂ_[l] := (x' : ℂ_[l]) - x with hy
  have hy1 : ‖y‖ < 1 := by
    have : y = ((x' : ℂ_[l]) - ξ) + (ξ - x) := by rw [hy]; ring
    rw [this]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx'd' ?_)
    rwa [norm_sub_rev]
  obtain ⟨k, hk, hexp⟩ := newton_expansion P hP x y hx hy1.le
  have hxy : x + y = (x' : ℂ_[l]) := by rw [hy]; ring
  rw [hxy, hP0, h0, zero_add] at hexp
  have hfac : y * (P.derivative.eval x + k * y) = 0 := by
    rw [hexp]; ring
  have hne : P.derivative.eval x + k * y ≠ 0 := by
    intro h
    have h6 : P.derivative.eval x = -(k * y) := eq_neg_of_add_eq_zero_left h
    rw [h6, norm_neg, norm_mul] at h1
    have : ‖k‖ * ‖y‖ < 1 := by
      calc ‖k‖ * ‖y‖ ≤ 1 * ‖y‖ := by gcongr
        _ < 1 := by rwa [one_mul]
    exact absurd h1 this.ne
  have hy0 : y = 0 := (mul_eq_zero.mp hfac).resolve_right hne
  have : x = (x' : ℂ_[l]) := by rw [← hxy, hy0, add_zero]
  rw [this]
  exact x'.2
end ReciprocityTheory.ChartRestriction.L1

-- Prove2me | solution 1 for UncoupledDyn.Continuum.U0_unique_nash
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:29:27.066995+00:00
-- url     : https://prove2.me/submissions/88fe32b9-ef0c-4d1c-9e7f-f6e8cc755e8e

import Mathlib
import Definitions.Def_UncoupledDyn_Continuum_Setting

namespace Aux_UD_U0
open UncoupledDyn.Continuum

theorem succ_ne (i : Fin 2) : i + 1 ≠ i := by fin_cases i <;> decide

theorem update_mem (x : Fin 2 → ℂ) (hx : x ∈ X) (i : Fin 2) (z : ℂ) (hz : z ∈ D) :
    Function.update x i z ∈ X := by
  rw [X, Set.mem_univ_pi] at hx ⊢
  intro j
  by_cases h : j = i
  · subst h; simp [hz]
  · rw [Function.update_of_ne h]; exact hx j

end Aux_UD_U0

open UncoupledDyn.Continuum Aux_UD_U0 in
theorem solution (ξ : Fin 2 → ℂ → ℂ)
    (hξ : ∀ i, ContinuousOn (ξ i) D ∧ Set.MapsTo (ξ i) D D)
    (huniq : ∀ i, ∃! z, z ∈ D ∧ ξ i (ξ (i + 1) z) = z)
    (G : Game) (hG : ∀ i, ∀ x ∈ X, G i x = -‖x i - ξ i (x (i + 1))‖ ^ 2)
    (xbar : Fin 2 → ℂ) (hxbar : ∀ i, xbar i ∈ D ∧ ξ i (ξ (i + 1) (xbar i)) = xbar i) :
    IsNash G xbar ∧ ∀ x, IsNash G x → x = xbar := by
  have hXbar : xbar ∈ X := by
    rw [X, Set.mem_univ_pi]; exact fun i => (hxbar i).1
  -- xbar is a mutual best response
  have hbr : ∀ i, xbar (i + 1) = ξ (i + 1) (xbar i) := by
    intro i
    have h11 : i + 1 + 1 = i := by fin_cases i <;> decide
    set y := ξ (i + 1) (xbar i) with hy
    have hyD : y ∈ D := (hξ (i + 1)).2 (hxbar i).1
    have hyfix : ξ (i + 1) (ξ (i + 1 + 1) y) = y := by
      rw [h11, hy, (hxbar i).2]
    have e1 := (huniq (i + 1)).unique ⟨hyD, hyfix⟩ (hxbar (i + 1))
    exact e1.symm
  have hbr' : ∀ i, xbar i = ξ i (xbar (i + 1)) := by
    intro i
    rw [hbr i, (hxbar i).2]
  -- Nash characterisation
  have char : ∀ x, IsNash G x → ∀ i, x i = ξ i (x (i + 1)) := by
    intro x hx i
    obtain ⟨hxX, hN⟩ := hx
    have hxX' := hxX
    rw [X, Set.mem_univ_pi] at hxX'
    set z := ξ i (x (i + 1)) with hz
    have hzD : z ∈ D := (hξ i).2 (hxX' (i + 1))
    have h := hN i z hzD
    rw [hG i _ (update_mem x hxX i z hzD), hG i x hxX] at h
    simp only [Function.update_self, Function.update_of_ne (succ_ne i)] at h
    rw [← hz, sub_self, norm_zero] at h
    have : ‖x i - z‖ ^ 2 ≤ 0 := by nlinarith
    have : ‖x i - z‖ = 0 := by nlinarith [norm_nonneg (x i - z)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  constructor
  · refine ⟨hXbar, fun i z hz => ?_⟩
    rw [hG i _ (update_mem xbar hXbar i z hz), hG i xbar hXbar, ← hbr' i, sub_self, norm_zero]
    have := sq_nonneg ‖Function.update xbar i z i - ξ i (Function.update xbar i z (i + 1))‖
    linarith
  · intro x hx
    have hc := char x hx
    have hxX := hx.1
    rw [X, Set.mem_univ_pi] at hxX
    funext i
    have h11 : i + 1 + 1 = i := by fin_cases i <;> decide
    have hfix : ξ i (ξ (i + 1) (x i)) = x i := by
      have := hc (i + 1)
      rw [h11] at this
      rw [← this, ← hc i]
    exact (huniq i).unique ⟨hxX i, hfix⟩ (hxbar i)

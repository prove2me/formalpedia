-- Prove2me | solution 1 for ResolvingPricing.eq_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:34:24.513201+00:00
-- url     : https://prove2.me/submissions/fca6c15a-e112-4cdf-acdf-21822c124e56

import Mathlib
import Definitions.Def_ResolvingPricing_Run

open MeasureTheory

open ResolvingPricing in
theorem solution (P : Model) (T : ℕ) (x : ℝ) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (π : Run P T x μ ℱ) (ω : Ω) (τ : ℕ) (hτ1 : 1 ≤ τ)
    (hτT : τ ≤ T) :
    π.xB τ ω = x - harm T (fun t => π.DeltaB t ω) τ - harm T (fun t => π.xiB t ω) τ
      + harm T (fun t => π.lostB t ω) τ := by
  have hmin : ∀ a y : ℝ, min a y = a - max (a - y) 0 := by
    intro a y
    rcases le_total a y with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  have hstep : ∀ s, 2 ≤ s → s ≤ T → π.xB (s - 1) ω
      = π.xB s ω - (π.DeltaB s ω + π.xiB s ω - π.lostB s ω) / ((s : ℝ) - 1) := by
    intro s hs2 hsT
    have e : T - (s - 1) = (T - s) + 1 := by omega
    have hc : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have hs2' : (2 : ℝ) ≤ s := by exact_mod_cast hs2
    have hs0 : (s : ℝ) ≠ 0 := by linarith
    have hs1 : (s : ℝ) - 1 ≠ 0 := by linarith
    simp only [Run.xB, Run.yB, Run.DeltaB, Run.lamB, Run.xiB, Run.lostB, e, Run.inv, hc]
    rw [hmin]
    field_simp <;> ring
  obtain ⟨r, rfl⟩ : ∃ r, τ = T - r := ⟨T - τ, by omega⟩
  have hr : r ≤ T - 1 := by omega
  have hT1n : 1 ≤ T := by omega
  clear hτ1 hτT
  induction r with
  | zero =>
    have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT1n
    have hT : (T : ℝ) ≠ 0 := by linarith
    simp only [Nat.sub_zero, harm, Finset.Ioc_self, Finset.sum_empty, sub_zero, add_zero]
    simp only [Run.xB, Run.yB, Nat.sub_self, Run.inv]
    field_simp
  | succ r ih =>
    have ih' := ih (by omega)
    have e1 : T - (r + 1) = (T - r) - 1 := by omega
    rw [e1, hstep (T - r) (by omega) (by omega), ih']
    have hI : Finset.Ioc (T - r - 1) T = insert (T - r) (Finset.Ioc (T - r) T) := by
      ext j; simp; omega
    have hnot : T - r ∉ Finset.Ioc (T - r) T := by simp
    simp only [harm, hI, Finset.sum_insert hnot]
    ring

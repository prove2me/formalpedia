-- Prove2me | solution 1 for SaysLaw.hoarding_permits_general_glut
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T20:07:39.188368+00:00
-- url     : https://prove2.me/submissions/408361d7-bf01-4372-aeff-78a5e20f4afd

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_SaysLaw_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open SaysLaw

theorem solution {ι G : Type*} [Fintype ι] [Nonempty ι] [Fintype G]
    (p : G → ℝ) (supply : ι → G → ℝ) (m : ι → ℝ) :
    ∃ (demand : ι → G → ℝ) (m' : ι → ℝ),
      MonetaryBudget p supply demand m m' ∧
        GeneralGlut (excessDemand supply demand) := by
  let demand : ι → G → ℝ := fun i g => supply i g - 1
  let m' : ι → ℝ := fun i => m i + ∑ g, p g
  refine ⟨demand, m', ?_, ?_⟩
  · intro i
    have hbundle : bundleValue p (demand i) =
        bundleValue p (supply i) - ∑ g, p g := by
      change (∑ g, p g * (supply i g - 1)) =
        (∑ g, p g * supply i g) - ∑ g, p g
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    change bundleValue p (demand i) + m' i =
      bundleValue p (supply i) + m i
    rw [hbundle]
    dsimp [m']
    ring
  · intro g
    change (∑ i, ((supply i g - 1) - supply i g)) < 0
    have hc : 0 < (Fintype.card ι : ℝ) :=
      Nat.cast_pos.mpr Fintype.card_pos
    calc
      (∑ i, ((supply i g - 1) - supply i g)) =
          ∑ i, (-1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = -(Fintype.card ι : ℝ) := by simp
      _ < 0 := by linarith

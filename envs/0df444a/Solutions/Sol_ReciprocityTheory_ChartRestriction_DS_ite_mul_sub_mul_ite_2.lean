-- Prove2me | solution 2 for ReciprocityTheory.ChartRestriction.DS.ite_mul_sub_mul_ite
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-23T22:38:19.922852+00:00
-- url     : https://prove2.me/submissions/b9d7623d-62a5-4dd7-89ac-3fc8e51204d2

import Mathlib.Algebra.Ring.Basic

theorem solution {R : Type*} [Ring R] (p : Prop) [Decidable p] (X Z : R) :
    (if p then X else 0) * Z - Z * (if p then X else 0) =
      if p then X * Z - Z * X else 0 := by
  by_cases h : p <;> simp [h]

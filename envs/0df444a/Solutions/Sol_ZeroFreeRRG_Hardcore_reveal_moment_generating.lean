-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.reveal_moment_generating
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:38:50.55017+00:00
-- url     : https://prove2.me/submissions/38aba497-9f86-4de3-b22b-471b93c94238

import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (n : ℕ) (s θ : ℝ) (z : Fin n → ℝ) :
    (∑ U : Finset (Fin n), revealProb s U * Real.exp (θ * ∑ v ∈ U, z v)) =
      ∏ v : Fin n, (s * Real.exp (θ*z v) + (1-s)) := by
  classical
  have hh := Finset.prod_add (fun v : Fin n => s * Real.exp (θ*z v)) (fun _ : Fin n => 1-s) Finset.univ
  simp only [Finset.powerset_univ,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_sdiff,
    Finset.inter_univ,Finset.card_univ,Fintype.card_fin] at hh
  symm
  calc
    _ = ∑ U : Finset (Fin n), (s ^ U.card * ∏ v ∈ U, Real.exp (θ*z v)) * (1-s)^(n-U.card) := hh
    _ = ∑ U : Finset (Fin n), revealProb s U * Real.exp (θ * ∑ v ∈ U, z v) := by
      apply Finset.sum_congr rfl
      intro U hU
      rw [← Real.exp_sum, ← Finset.mul_sum]
      unfold revealProb
      ring

-- Prove2me | solution 1 for PoWMining.Investment.invested_cost_order
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:34:09.365888+00:00
-- url     : https://prove2.me/submissions/93f94fe7-c495-4607-811f-7e9f7359e9ad

import Mathlib
import Definitions.Def_PoWMining_Investment_Model

set_option autoImplicit false
open PoWMining.Investment

theorem solution {N : ℕ} (P : InvParams N) (hP : P.Standing) (hη : 0 < P.η) :
    ∀ i j : Fin N, P.ct i < P.ct j →
      cost P (fun _ => betaBar P) i < cost P (fun _ => betaBar P) j := by
  intro i j hij
  have hbp : 0 < betaBar P := by
    unfold betaBar; split_ifs
    · norm_num
    · positivity
  have hb1 : betaBar P ≤ 1 := by
    unfold betaBar; split_ifs with h
    · exact le_rfl
    · rw [div_le_one hη]; linarith [not_le.mp h]
  have hηb : P.η * betaBar P ≤ 1 := by
    unfold betaBar; split_ifs with h
    · linarith
    · field_simp; exact le_rfl
  -- cost = c0 + (ct - c0) * (1 - b + η b²/2) with factor positive
  have hfac : 0 < 1 - betaBar P + P.η * betaBar P ^ 2 / 2 := by
    nlinarith [mul_nonneg hbp.le (sub_nonneg.mpr hηb), sq_nonneg (betaBar P)]
  have e : ∀ k : Fin N, cost P (fun _ => betaBar P) k =
      P.c0 + (P.ct k - P.c0) * (1 - betaBar P + P.η * betaBar P ^ 2 / 2) := by
    intro k; simp only [cost]; ring
  rw [e i, e j]
  nlinarith [mul_pos (sub_pos.mpr hij) hfac]

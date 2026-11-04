-- Prove2me | solution 1 for ReusablePricing.DPC.eq_EC14
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T03:52:08.056421+00:00
-- url     : https://prove2.me/submissions/f792da9e-852b-46e0-9ab4-157667501f46

import Mathlib
import Definitions.Def_ReusablePricing_DPC_Model
import Definitions.Def_ReusablePricing_DPC_Control
import Theorems.Thm_ReusablePricing_DPC_lemma_EC1

open Finset ReusablePricing.DPC

theorem solution (P : Basic) (φL φU Ψ R : ℝ) (nl : ℕ) (ε δ : ℝ)
    (hP : P.Standing φL φU Ψ R nl)
    (hε : ε ≤ min φL φU * nl)
    (hδ : δ = ((nl : ℝ) - 1) * (ε - 1) / (3 * nl))
    (ω : P.Path) (hω : 0 < P.pathProb ε nl ω) (hG : P.InG ε nl δ ω) :
    ∀ t ∈ Icc 1 P.T, ∀ j,
      P.dpcRate ε nl t ω j = P.lamD t j - ε / nl * (if 0 < P.lamD t j then 1 else 0) := by
  intro t ht j
  have h1 := lemma_EC1 P φL φU Ψ R nl ε δ hP hε hδ ω hω hG t ht
  obtain ⟨hMF, hOpt, -⟩ := id hP
  obtain ⟨-, -, -, -, -, hA1, -, -, hU0, -, -⟩ := id hMF
  have hcap : ∀ i, (P.A i j : ℝ) ≤ P.freeCap t ω i := by
    intro i
    have : (P.A i j : ℝ) ≤ 1 := by exact_mod_cast hA1 i j
    linarith [h1.1 i]
  unfold Basic.dpcRate
  rw [if_pos hcap]
  have h0 : 0 ≤ P.lamD t j := (hOpt.1.1 t ht j).1
  by_cases hpos : 0 < P.lamD t j
  · rw [if_pos hpos, mul_one]
    obtain ⟨ha, hb⟩ := h1.2 j hpos
    rw [min_eq_right hb.le, max_eq_right ha.le]
  · rw [if_neg hpos, mul_zero, sub_zero]
    have : P.lamD t j = 0 := le_antisymm (not_lt.mp hpos) h0
    rw [this]
    have hU : 0 ≤ P.lamU := hU0.le
    simp [hU]

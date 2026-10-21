-- Prove2me | solution 1 for PriceMatchNeg.Symmetric.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T11:54:34.47261+00:00
-- url     : https://prove2.me/submissions/1800aabf-fb77-4566-89f1-177ead09b6c6

import Mathlib
import Definitions.Def_PriceMatchNeg_Symmetric_Model
import Theorems.Thm_PriceMatchNeg_Symmetric_sn_equilibrium
import Theorems.Thm_PriceMatchNeg_Symmetric_pm_equilibrium
import Theorems.Thm_PriceMatchNeg_Symmetric_price_ordering
import Theorems.Thm_PriceMatchNeg_Symmetric_diagonal_profits

open PriceMatchNeg.Symmetric

theorem solution (P : Params) (hS : P.Standing) (θ : ℝ) (hθ : ValidPower θ) :
    (∃ w1 w2, IsSNEq P θ θ w1 w2) ∧ (∃ w, IsPMPrice P θ θ w) ∧
    ∀ w1 w2 w, IsSNEq P θ θ w1 w2 → IsPMPrice P θ θ w →
      piS P w1 w2 < piS P w w ∧ piB P w w < piB P w1 w2 ∧ piB P w w < piB P w2 w1 := by
  have hsn := sn_equilibrium P hS θ hθ
  have hpm := pm_equilibrium P hS θ θ hθ hθ
  obtain ⟨hpos, hlt, hhalf⟩ := price_ordering P hS θ hθ
  obtain ⟨-, hmono, -, hanti⟩ := diagonal_profits P hS
  have ha : 0 < P.a := hS.1
  refine ⟨⟨wSN P θ, wSN P θ, (hsn _ _).2 ⟨rfl, rfl⟩⟩, ⟨wPM P θ θ, (hpm _).2 rfl⟩, ?_⟩
  intro w1 w2 w h1 h2
  obtain ⟨rfl, rfl⟩ := (hsn _ _).1 h1
  obtain rfl := (hpm _).1 h2
  have hSNmem : wSN P θ ∈ Set.Icc 0 (P.a / 2) := ⟨hpos.le, by linarith⟩
  have hPMmem : wPM P θ θ ∈ Set.Icc 0 (P.a / 2) := ⟨by linarith, hhalf⟩
  have hSNmem' : wSN P θ ∈ Set.Icc 0 P.a := ⟨hpos.le, by linarith⟩
  have hPMmem' : wPM P θ θ ∈ Set.Icc 0 P.a := ⟨by linarith, by linarith⟩
  have hB := hanti hSNmem' hPMmem' hlt
  exact ⟨hmono hSNmem hPMmem hlt, hB, hB⟩

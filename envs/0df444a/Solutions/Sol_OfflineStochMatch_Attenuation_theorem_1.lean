-- Prove2me | solution 1 for OfflineStochMatch.Attenuation.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T07:28:37.00616+00:00
-- url     : https://prove2.me/submissions/b4846292-6b0c-4588-a7bb-70c1dd339633
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OfflineStochMatch_Attenuation_Setting
import Theorems.Thm_OfflineStochMatch_Attenuation_eq_7
import Theorems.Thm_OfflineStochMatch_Attenuation_effective_exp_lin
import Theorems.Thm_OfflineStochMatch_Attenuation_safe_bound

open OfflineStochMatch.Attenuation in
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (hG : Function.Injective G.ends)
    (p y : E → ℝ) (t : V → ℕ∞) (aT : ℝ → ℝ)
    (hp : ∀ f, 0 ≤ p f ∧ p f ≤ 1) (ht : ∀ v, 2 ≤ t v) (hy : LPFeasible G p t y)
    (haT : aT = expAtt (1 / 2) ∨ aT = linAtt (1 / 2)) (e : E) :
    betaStar ≤ attProb aT p y e * probFree G p t y aT e := by
  have hrange : ∀ z ∈ Set.Icc (0 : ℝ) 1, aT z ∈ Set.Icc (0 : ℝ) 1 := by
    rcases haT with h | h <;> subst h
    · exact effective_exp_lin.1.1
    · exact effective_exp_lin.2.1
  have h7 := eq_7 G p y t aT hp hy.1 hrange e
  have hs := safe_bound G hG p y t aT hp ht hy haT e
  exact le_trans hs h7

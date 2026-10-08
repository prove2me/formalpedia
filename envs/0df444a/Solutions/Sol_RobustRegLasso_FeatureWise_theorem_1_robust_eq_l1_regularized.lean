-- Prove2me | solution 1 for RobustRegLasso.FeatureWise.theorem_1_robust_eq_l1_regularized
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T03:33:06.015983+00:00
-- url     : https://prove2.me/submissions/484f4920-0e73-46be-9b64-3aa129312e75

import Mathlib
import Definitions.Def_RobustRegLasso_FeatureWise_Basic
import Theorems.Thm_RobustRegLasso_FeatureWise_per_x_identity

open RobustRegLasso.FeatureWise

theorem solution {n m : ℕ} (hn : 0 < n)
    (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : EuclideanSpace ℝ (Fin n)) (c : Fin m → ℝ)
    (hc : ∀ i, 0 ≤ c i) :
    (∀ x : Fin m → ℝ, IsMinOn (robustObjective a b c) Set.univ x ↔
        IsMinOn (l1RegularizedObjective a b c) Set.univ x) ∧
      ⨅ x : Fin m → ℝ, robustObjective a b c x =
        ⨅ x : Fin m → ℝ, ((l1RegularizedObjective a b c x : ℝ) : EReal) := by
  have hid (x : Fin m → ℝ) :
      robustObjective a b c x = ((l1RegularizedObjective a b c x : ℝ) : EReal) :=
    (per_x_identity hn a b c hc x).2
  constructor
  · intro x
    simp only [isMinOn_univ_iff, hid, EReal.coe_le_coe_iff]
  · exact iInf_congr hid

#print axioms solution

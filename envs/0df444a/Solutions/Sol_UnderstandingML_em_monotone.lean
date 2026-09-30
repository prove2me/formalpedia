-- Prove2me | solution 1 for UnderstandingML.em_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T15:33:47.626988+00:00
-- url     : https://prove2.me/submissions/5b373767-1ba0-49c5-92cc-dad9d63cb9c1

import Definitions.Def_UnderstandingML_Generative
import Theorems.Thm_UnderstandingML_em_alternate_max

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

open UnderstandingML

theorem solution {Θ X : Type*} {k m : ℕ} (p : Θ → X → Fin k → ℝ)
    (hp : ∀ θ x y, 0 < p θ x y) (x : Fin m → X) (θ : ℕ → Θ) (hθ : IsEMSequence p x θ) (t : ℕ) :
    latentLogLik p x (θ t) ≤ latentLogLik p x (θ (t + 1)) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp [latentLogLik]
  obtain ⟨h1, h2, h3⟩ := em_alternate_max p hp x
  set Q : Fin m → Fin k → ℝ := fun i y ↦ posterior p (θ t) (x i) y
  have hQ : IsRowStochastic Q := by
    refine ⟨fun i y ↦ ?_, fun i ↦ ?_⟩
    · exact div_nonneg (hp _ _ _).le (Finset.sum_nonneg fun y _ ↦ (hp _ _ _).le)
    · have hS : 0 < ∑ y, p (θ t) (x i) y :=
        Finset.sum_pos (fun y _ ↦ hp _ _ y) ⟨⟨0, hk⟩, Finset.mem_univ _⟩
      simp only [Q, posterior, ← Finset.sum_div, div_self hS.ne']
  calc latentLogLik p x (θ t) = emG p x Q (θ t) := (h2 (θ t)).symm
    _ ≤ emG p x Q (θ (t + 1)) := (h3 Q _ _).2 (hθ t (θ t))
    _ ≤ latentLogLik p x (θ (t + 1)) := h1 Q _ hQ

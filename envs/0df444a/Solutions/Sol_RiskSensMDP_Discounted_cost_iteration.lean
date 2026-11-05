-- Prove2me | solution 1 for RiskSensMDP.Discounted.cost_iteration
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T02:17:27.810021+00:00
-- url     : https://prove2.me/submissions/94c44661-dc28-41cf-89ed-549e98b665a8

import Mathlib
import Definitions.Def_RiskSensMDP_Discounted_Model

open MeasureTheory ProbabilityTheory Filter
open RiskSensMDP.Discounted

namespace RSMDP2CostAux

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

lemma dHC_append (M : Model E A) (l : List (E × A)) (p : E × A) :
    discountedHistoryCost M (l ++ [p]) =
      discountedHistoryCost M l + M.β ^ l.length * M.c p := by
  induction l with
  | nil => simp [discountedHistoryCost]
  | cons q l ih =>
    simp only [List.cons_append, discountedHistoryCost, ih, List.length_cons, pow_succ]
    ring

lemma claim (M : Model E A) (π : MarkovPolicy M) (y z : ℝ) :
    ∀ (n k : ℕ) (h : History E A) (y' z' : ℝ),
      h.1.length = k → y' = y + z * discountedHistoryCost M h.1 → z' = z * M.β ^ k →
      expectedFrom M (historyRule M π y z) k h n y' z' =
        policyIteration M (fun j => π (j + k)) n (h.2, (y', z')) := by
  intro n
  induction n with
  | zero =>
    intro k h y' z' _ _ _
    simp [expectedFrom, policyIteration, terminal]
  | succ n ih =>
    intro k h y' z' hl hy hz
    rw [expectedFrom]
    have ha : historyRule M π y z k h = (π k).f (h.2, (y', z')) := by
      simp only [historyRule, hy, hz]
    have key : ∀ x', expectedFrom M (historyRule M π y z) (k + 1)
        (h.1 ++ [(h.2, historyRule M π y z k h)], x') n
        (y' + z' * M.c (h.2, historyRule M π y z k h)) (z' * M.β) =
        policyIteration M (fun j => π (j + (k + 1))) n
          (x', (y' + z' * M.c (h.2, historyRule M π y z k h), z' * M.β)) := by
      intro x'
      apply ih
      · simp [hl]
      · simp only [dHC_append, hl, hy, hz]; ring
      · rw [hz, pow_succ]; ring
    rw [integral_congr_ae (ae_of_all _ key)]
    have hπ : (fun j => (fun j => π (j + k)) (j + 1)) = fun j => π (j + (k + 1)) := by
      funext j; show π (j + 1 + k) = π (j + (k + 1)); rw [show j + 1 + k = j + (k + 1) by omega]
    simp only [policyIteration, decisionOperator, oneStep, hπ, Nat.zero_add]
    rw [ha]

end RSMDP2CostAux

theorem solution {E A : Type*}
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.MetrizableSpace E] [SecondCountableTopology E]
    [StandardBorelSpace E]
    [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [StandardBorelSpace A]
    (M : Model E A) (hBounds : HasBounds M) (hCC : HasCC M)
    (N : ℕ) (π : MarkovPolicy M) :
    ∀ n ∈ Finset.Icc 1 N, ∀ s ∈ extendedDomain E,
      markovValue M π n s.1 s.2.1 s.2.2 = policyIteration M π n s := by
  intro n _ s _
  have := RSMDP2CostAux.claim M π s.2.1 s.2.2 n 0 ([], s.1) s.2.1 s.2.2 rfl
    (by simp [discountedHistoryCost]) (by simp)
  simpa [markovValue] using this

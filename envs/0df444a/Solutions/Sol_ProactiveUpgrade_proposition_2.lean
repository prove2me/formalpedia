-- Prove2me | solution 1 for ProactiveUpgrade.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:34:02.997448+00:00
-- url     : https://prove2.me/submissions/b362bd22-3e92-44f2-b0e3-972634f51c80

import Mathlib
import Definitions.Def_ProactiveUpgrade_Model
import Definitions.Def_ProactiveUpgrade_vhat
import Definitions.Def_ProactiveUpgrade_IsValid
import Definitions.Def_ProactiveUpgrade_subOperators

namespace Aux_PU2

lemma maxmix (N A q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    max N (q * A + (1 - q) * N) = (1 - q) * N + q * max N A := by
  rcases le_total N A with h | h
  · rw [max_eq_right h, max_eq_right (by nlinarith)]; ring
  · rw [max_eq_left h, max_eq_left (by nlinarith)]; ring

end Aux_PU2

open ProactiveUpgrade in
theorem solution {m : ℕ} (M : Model m) (hM : IsValid M) (T t : ℕ) (ht1 : 1 ≤ t)
    (htT : t ≤ T) (x : Fin m → ℕ) :
    vhat M T t x =
      ∑ i, M.lam * M.β i * qbar M i * TP M (vhat M T (t + 1)) x i +
        ∑ i, (if h : i.val + 1 < m then
          M.lam * M.β i * M.q i * TU M (vhat M T (t + 1)) x i h else 0) +
        (M.lam * M.β0 + (1 - M.lam)) * vhat M T (t + 1) x := by
  have hT1 : T + 1 - t = (T - t) + 1 := by omega
  have hT2 : T + 1 - (t + 1) = T - t := by omega
  unfold vhat
  rw [hT1, hT2]
  show step M (valueToGo M (T - t)) x = _
  obtain ⟨f, hf⟩ : ∃ f, f = valueToGo M (T - t) := ⟨_, rfl⟩
  rw [← hf]
  unfold step
  rw [← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  unfold reqOp qbar
  by_cases h : i.val + 1 < m
  · simp only [h, ↓reduceDIte, ↓reduceIte]
    obtain ⟨hq0, hq1⟩ := hM.q_mem i h
    have key : (if x (succIdx i h) = 0 then noOfferVal M f x i
        else max (noOfferVal M f x i) (offerVal M f x i h)) =
        (1 - M.q i) * TP M f x i + M.q i * TU M f x i h := by
      unfold offerVal TP TU noOfferVal
      by_cases h1 : x (succIdx i h) = 0
      · by_cases h2 : x i = 0
        · simp only [h1, h2, ↓reduceIte]; ring
        · simp only [h1, h2, ↓reduceIte]; ring
      · by_cases h2 : x i = 0
        · simp only [h1, h2, ↓reduceIte]
          rw [Aux_PU2.maxmix _ _ _ hq0 hq1]
        · simp only [h1, h2, ↓reduceIte]
          rw [Aux_PU2.maxmix _ _ _ hq0 hq1, ← max_add_add_right]
    rw [key]; ring
  · simp only [h, ↓reduceDIte, ↓reduceIte, TP, noOfferVal]
    ring

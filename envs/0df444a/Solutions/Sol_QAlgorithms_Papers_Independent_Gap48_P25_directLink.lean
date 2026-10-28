-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P25.directLink
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T23:15:34.252091+00:00
-- url     : https://prove2.me/submissions/b17132f5-6e6b-4da3-ba4c-9b3eeee53291

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

open QAlgorithms.Papers.Independent.Gap48.P25
noncomputable section


open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- Eq.(B1), PDF p.46: direct-link coincidence rate, with eta^2 and total loss t. -/
theorem solution (nu t eta : ℝ) (hnu : 0 < nu) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (heta : 0 < eta ∧ eta ≤ 1) :
    (∀ b, 0 ≤ directLaw t eta b) ∧ (∑ b : Fin 3 → Bool, directLaw t eta b) = 1 ∧
    directRate nu t eta = nu*t*eta^2 := by
  have hg : ∀ b : Fin 3 → Bool, directLaw t eta b =
      ∏ i : Fin 3, (if i = 0 then (if b i then t else 1-t) else (if b i then eta else 1-eta)) := by
    intro b; simp [directLaw, Fin.prod_univ_three]
  refine ⟨fun b => ?_, ?_, ?_⟩
  · unfold directLaw
    have h1 : 0 ≤ (if b 0 then t else 1-t) := by split_ifs <;> linarith [ht.1, ht.2]
    have h2 : 0 ≤ (if b 1 then eta else 1-eta) := by split_ifs <;> linarith [heta.1, heta.2]
    have h3 : 0 ≤ (if b 2 then eta else 1-eta) := by split_ifs <;> linarith [heta.1, heta.2]
    positivity
  · simp_rw [hg]
    rw [← Fintype.prod_sum (fun (i : Fin 3) (x : Bool) =>
      if i = 0 then (if x then t else 1-t) else (if x then eta else 1-eta))]
    refine Finset.prod_eq_one fun i _ => ?_
    split_ifs <;> simp
  · unfold directRate
    have : ∀ b : Fin 3 → Bool, (if (∀ i, b i = true) then directLaw t eta b else 0) =
        if b = (fun _ => true) then directLaw t eta b else 0 := by
      intro b; congr 1; simp [funext_iff]
    simp_rw [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp [directLaw]; ring




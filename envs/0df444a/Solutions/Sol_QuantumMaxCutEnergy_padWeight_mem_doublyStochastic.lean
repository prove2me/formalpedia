-- Prove2me | solution 1 for QuantumMaxCutEnergy.padWeight_mem_doublyStochastic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T02:20:22.129924+00:00
-- url     : https://prove2.me/submissions/406ab86c-44e1-4ecb-b4de-bc142f2b0df7

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutMatchingPadding
import Theorems.Thm_QuantumMaxCutEnergy_loadAt_eq_sum_pairWeight
import Mathlib

set_option autoImplicit false
open scoped BigOperators

namespace QuantumMaxCutEnergy

lemma pairWeight_nonneg {n : ℕ} (x : Edge n → ℝ) (hx : ∀ e, 0 ≤ x e) (a b : Fin n) :
    0 ≤ pairWeight x a b := by
  unfold pairWeight
  split_ifs with h1 h2
  · exact hx _
  · exact hx _
  · exact le_rfl

lemma padWeight_symm {n : ℕ} (x : Edge n → ℝ) (a b : Fin n) :
    padWeight x a b = padWeight x b a := by
  by_cases h : a = b
  · subst h; rfl
  · rw [padWeight_apply_of_ne x h, padWeight_apply_of_ne x (Ne.symm h), pairWeight_comm]

lemma padWeight_nonneg {n : ℕ} (x : Edge n → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v, loadAt x v ≤ 1) (a b : Fin n) : 0 ≤ padWeight x a b := by
  by_cases h : a = b
  · subst h
    rw [padWeight_apply_self]
    linarith [hload a]
  · rw [padWeight_apply_of_ne x h]
    exact pairWeight_nonneg x hx a b

lemma padWeight_row_sum {n : ℕ} (x : Edge n → ℝ) (a : Fin n) :
    ∑ b, padWeight x a b = 1 := by
  have hsplit : ∑ b, padWeight x a b
      = (∑ b, (if a = b then (1 - loadAt x a) else 0)) + ∑ b, (if a = b then 0 else pairWeight x a b) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun b _ => by
      by_cases h : a = b <;> simp [padWeight, h])
  have hdiag : ∑ b, (if a = b then (1 - loadAt x a) else 0) = 1 - loadAt x a := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb; rw [if_neg (Ne.symm hb)]
    · intro h; exact absurd (Finset.mem_univ a) h
  have hoff : ∑ b, (if a = b then (0 : ℝ) else pairWeight x a b) = loadAt x a := by
    rw [loadAt_eq_sum_pairWeight]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases h : a = b
    · subst h; rw [if_pos rfl, pairWeight_self]
    · rw [if_neg h]
  rw [hsplit, hdiag, hoff]
  ring

lemma padWeight_col_sum {n : ℕ} (x : Edge n → ℝ) (a : Fin n) :
    ∑ b, padWeight x b a = 1 := by
  rw [show (∑ b, padWeight x b a) = ∑ b, padWeight x a b from
    Finset.sum_congr rfl (fun b _ => padWeight_symm x b a)]
  exact padWeight_row_sum x a

end QuantumMaxCutEnergy

open QuantumMaxCutEnergy

/-- The symmetric padding of a point of the load polytope is doubly stochastic. -/
theorem solution {n : ℕ} (x : Edge n → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v, loadAt x v ≤ 1) :
    padWeight x ∈ doublyStochastic ℝ (Fin n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b; exact padWeight_nonneg x hx hload a b
  · funext a
    have h1 : (padWeight x).mulVec (1 : Fin n → ℝ) a = ∑ b, padWeight x a b := by
      simp [Matrix.mulVec, dotProduct]
    rw [h1, padWeight_row_sum]
    simp
  · funext a
    have h1 : Matrix.vecMul (1 : Fin n → ℝ) (padWeight x) a = ∑ b, padWeight x b a := by
      simp [Matrix.vecMul, dotProduct]
    rw [h1, padWeight_col_sum]
    simp




#print axioms solution

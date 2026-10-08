-- Prove2me | solution 1 for PriceOfStability.WeightedPotential.join_shared_edge
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-05T10:59:37.418525+00:00
-- url     : https://prove2.me/submissions/13453781-d5e8-4138-9750-eb44adb0f3fc

import Definitions.Def_PriceOfStability_WeightedPotential_Model

open PriceOfStability.WeightedPotential

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

private lemma users_join (S : ι → Finset E) (i : ι) (T : Finset E) (e : E)
    (heT : e ∈ T) :
    users (Function.update S i T) e = insert i (users S e) := by
  ext k
  by_cases hki : k = i
  · subst k
    simp [users, heT]
  · simp [users, Function.update_of_ne hki, hki]

theorem solution (G : WeightedGame ι E) (hG : G.IsStandard)
    (hspace : ∀ e, (Finset.univ.filter (fun i => e ∈ strategySpace G i)).card ≤ 2)
    (S : ι → Finset E) (hS : IsProfile G S) (i j : ι) (hij : i ≠ j)
    (T : Finset E) (hT : T ∈ G.strategies i) (e : E)
    (hjoin : users S e = {j}) (heT : e ∈ T) :
    edgePotential G (Function.update S i T) e - edgePotential G S e
        = G.edgeCost e * G.weight i ^ 2 / (G.weight i + G.weight j) ∧
      edgePotential G (Function.update S i T) e - edgePotential G S e
        = G.weight i * (G.weight i / edgeWeight G (Function.update S i T) e * G.edgeCost e) := by
  have hnew : users (Function.update S i T) e = {i, j} := by
    rw [users_join S i T e heT, hjoin]
  have holdWeight : edgeWeight G S e = G.weight j := by
    change (∑ k ∈ users S e, G.weight k) = _
    simp [hjoin]
  have hnewWeight : edgeWeight G (Function.update S i T) e = G.weight i + G.weight j := by
    change (∑ k ∈ users (Function.update S i T) e, G.weight k) = _
    simp [hnew, hij]
  have hden : G.weight i + G.weight j ≠ 0 := by
    have hi := hG.1 i
    have hj := hG.1 j
    linarith
  simp only [edgePotential, hjoin, hnew, holdWeight, hnewWeight]
  simp [hij]
  constructor <;> field_simp <;> ring

#print axioms solution

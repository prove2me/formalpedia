-- Prove2me | solution 1 for PriceOfStability.WeightedPotential.potential_change
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-05T10:59:41.783365+00:00
-- url     : https://prove2.me/submissions/475b443d-c799-4e07-9e17-4479380ce3a4

import Theorems.Thm_PriceOfStability_WeightedPotential_join_shared_edge

open PriceOfStability.WeightedPotential

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

private lemma profile_update (G : WeightedGame ι E) (S : ι → Finset E)
    (hS : IsProfile G S) (i : ι) (T : Finset E) (hT : T ∈ G.strategies i) :
    IsProfile G (Function.update S i T) := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa using hT
  · simpa [Function.update_of_ne hji] using hS j

private lemma users_card_le (G : WeightedGame ι E)
    (hspace : ∀ e, (Finset.univ.filter (fun i => e ∈ strategySpace G i)).card ≤ 2)
    (S : ι → Finset E) (hS : IsProfile G S) (e : E) : (users S e).card ≤ 2 := by
  apply le_trans (Finset.card_le_card ?_) (hspace e)
  intro j hj
  simp only [users, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, strategySpace, Finset.mem_biUnion]
  exact ⟨S j, hS j, hj⟩

private lemma users_join (S : ι → Finset E) (i : ι) (T : Finset E) (e : E)
    (heT : e ∈ T) : users (Function.update S i T) e = insert i (users S e) := by
  ext k
  by_cases hki : k = i
  · subst k
    simp [users, heT]
  · simp [users, Function.update_of_ne hki, hki]

private lemma edge_join_change (G : WeightedGame ι E) (hG : G.IsStandard)
    (hspace : ∀ e, (Finset.univ.filter (fun i => e ∈ strategySpace G i)).card ≤ 2)
    (S : ι → Finset E) (hS : IsProfile G S) (i : ι) (T : Finset E)
    (hT : T ∈ G.strategies i) (e : E) (heS : e ∉ S i) (heT : e ∈ T) :
    edgePotential G (Function.update S i T) e - edgePotential G S e =
      G.weight i * (G.weight i / edgeWeight G (Function.update S i T) e * G.edgeCost e) := by
  have hni : i ∉ users S e := by simpa [users] using heS
  have hbound := users_card_le G hspace (Function.update S i T)
    (profile_update G S hS i T hT) e
  rw [users_join S i T e heT, Finset.card_insert_of_notMem hni] at hbound
  by_cases hzero : users S e = ∅
  · have hnew : users (Function.update S i T) e = {i} := by
      simp [users_join S i T e heT, hzero]
    have hw0 : edgeWeight G S e = 0 := by
      change (∑ k ∈ users S e, G.weight k) = 0
      simp [hzero]
    have hw1 : edgeWeight G (Function.update S i T) e = G.weight i := by
      change (∑ k ∈ users (Function.update S i T) e, G.weight k) = _
      simp [hnew]
    have hwi : G.weight i ≠ 0 := by have hi := hG.1 i; linarith
    simp [edgePotential, hzero, hnew, hw0, hw1, hwi, mul_comm]
  · have hc : (users S e).card ≠ 0 := fun hc => hzero (Finset.card_eq_zero.mp hc)
    have hone : (users S e).card = 1 := by omega
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hone
    have hij : i ≠ j := by simpa [hj] using hni
    exact (PriceOfStability.WeightedPotential.join_shared_edge
      G hG hspace S hS i j hij T hT e hj heT).2

private lemma users_unchanged (S : ι → Finset E) (i : ι) (T : Finset E) (e : E)
    (h : e ∈ S i ↔ e ∈ T) : users (Function.update S i T) e = users S e := by
  ext k
  by_cases hki : k = i
  · subst k
    simpa [users] using h.symm
  · simp [users, Function.update_of_ne hki]

private lemma edge_change (G : WeightedGame ι E) (hG : G.IsStandard)
    (hspace : ∀ e, (Finset.univ.filter (fun i => e ∈ strategySpace G i)).card ≤ 2)
    (S : ι → Finset E) (hS : IsProfile G S) (i : ι) (T : Finset E)
    (hT : T ∈ G.strategies i) (e : E) :
    edgePotential G (Function.update S i T) e - edgePotential G S e =
      G.weight i *
        ((if e ∈ (Function.update S i T) i then
            G.weight i / edgeWeight G (Function.update S i T) e * G.edgeCost e else 0) -
          (if e ∈ S i then G.weight i / edgeWeight G S e * G.edgeCost e else 0)) := by
  by_cases heS : e ∈ S i <;> by_cases heT : e ∈ T
  · have hu := users_unchanged S i T e (by simp [heS, heT])
    have hw : edgeWeight G (Function.update S i T) e = edgeWeight G S e := by
      change (∑ k ∈ users (Function.update S i T) e, G.weight k) =
        (∑ k ∈ users S e, G.weight k)
      rw [hu]
    simp [edgePotential, hu, hw, heS, heT]
  · have hnew := profile_update G S hS i T hT
    have hnot : e ∉ (Function.update S i T) i := by simpa using heT
    have hrev := edge_join_change G hG hspace (Function.update S i T) hnew
      i (S i) (hS i) e hnot heS
    simp only [Function.update_idem, Function.update_eq_self] at hrev
    simp only [Function.update_self, heS, heT, if_true, if_false]
    linarith
  · have hj := edge_join_change G hG hspace S hS i T hT e heS heT
    simpa [heS, heT] using hj
  · have hu := users_unchanged S i T e (by simp [heS, heT])
    have hw : edgeWeight G (Function.update S i T) e = edgeWeight G S e := by
      change (∑ k ∈ users (Function.update S i T) e, G.weight k) =
        (∑ k ∈ users S e, G.weight k)
      rw [hu]
    simp [edgePotential, hu, hw, heS, heT]

private lemma payment_as_sum (G : WeightedGame ι E) (S : ι → Finset E) (i : ι) :
    payment G S i = ∑ e, if e ∈ S i then G.weight i / edgeWeight G S e * G.edgeCost e else 0 := by
  rw [← Finset.sum_filter]
  simp [payment, Finset.filter_mem_eq_inter]

theorem solution (G : WeightedGame ι E) (hG : G.IsStandard)
    (hspace : ∀ e, (Finset.univ.filter (fun i => e ∈ strategySpace G i)).card ≤ 2)
    (S : ι → Finset E) (hS : IsProfile G S) (i : ι) (T : Finset E) (hT : T ∈ G.strategies i) :
    potential G (Function.update S i T) - potential G S
      = G.weight i * (payment G (Function.update S i T) i - payment G S i) := by
  rw [potential, potential, ← Finset.sum_sub_distrib,
    payment_as_sum, payment_as_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  exact edge_change G hG hspace S hS i T hT e

#print axioms solution

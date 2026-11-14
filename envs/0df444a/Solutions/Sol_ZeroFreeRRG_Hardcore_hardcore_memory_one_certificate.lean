-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_memory_one_certificate
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:36:05.614283+00:00
-- url     : https://prove2.me/submissions/55d0819d-f596-4c95-9115-365600020091

import Theorems.Thm_LocalLemmaHierarchy_Completeness_theorem_1_1
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open LocalLemmaHierarchy.Completeness
open scoped Classical BigOperators

private theorem parent {V : Type} [Fintype V] (G : SimpleGraph V) (o : NeighborOrders G)
    (s : Hist (indRep G o)) (hex : IsExact (indRep G o) Set.univ s)
    (hlen : s.moves.length = 1) :
    ∃ v ∈ G.neighborFinset s.endpoint, v ∈ deleted (indRep G o) s.moves := by
  classical
  rcases s with ⟨start, ms⟩
  cases ms with
  | nil => simp at hlen
  | cons m rest =>
    have hr : rest = [] := by simpa using hlen
    subst rest
    have hl := hex.2 0 (by simp)
    simp only [List.take_zero, List.getElem_cons_zero] at hl
    rcases m with ⟨v,a,u⟩
    have hadj : G.Adj v u := by
      have hu := hl.2.2.1
      simp only [indRep, Finset.coe_insert, Set.mem_inter_iff, Set.mem_insert_iff,
        SimpleGraph.mem_neighborFinset, Set.mem_diff, Set.mem_univ, true_and] at hu
      rcases hu.1 with h | h
      · exact (hl.2.2.2 h).elim
      · change u ∈ G.neighborFinset v at h
        simpa only [SimpleGraph.mem_neighborFinset] using h
    refine ⟨v,?_,?_⟩
    · change v ∈ G.neighborFinset u
      simpa using hadj.symm
    · change v ∈ deleted (indRep G o) [⟨v,a,u⟩]
      simp [deleted,departure]

private theorem row {V : Type} [Fintype V] (G : SimpleGraph V) (o : NeighborOrders G)
    (p c r : ℝ) (s : Hist (indRep G o)) :
    let x := fun s : Hist (indRep G o) => if s.moves = [] then r else c
    let F := G.neighborFinset s.endpoint \ deleted (indRep G o) s.moves
    memUpdate (indRep G o) 1 (fun _ => p) x s =
      if s.endpoint ∈ deleted (indRep G o) s.moves then 0 else p * ((1-c)⁻¹) ^ F.card := by
  classical
  dsimp only
  let x := fun s : Hist (indRep G o) => if s.moves = [] then r else c
  have hx (a : (indRep G o).Opt s.endpoint) (u : V) : x (memStar 1 s a u) = c := by
    dsimp [x]
    have hh : (memStar 1 s a u).moves.length = 1 := by dsimp [memStar,Hist.suffix,Hist.append]; simp
    have hn : (memStar 1 s a u).moves ≠ [] := by intro he; simp [he] at hh
    rw [if_neg hn]
  change memUpdate (indRep G o) 1 (fun _ => p) x s = _
  unfold memUpdate
  simp only [hx]
  have hself : s.endpoint ∉ G.neighborFinset s.endpoint := by simp
  have hF : G.neighborFinset s.endpoint \ insert s.endpoint (deleted (indRep G o) s.moves) =
      G.neighborFinset s.endpoint \ deleted (indRep G o) s.moves := Finset.sdiff_insert_of_notMem hself _
  by_cases h : s.endpoint ∈ deleted (indRep G o) s.moves
  · simp only [indRep] at h
    simp [indRep,Finset.disjoint_singleton_left,Finset.insert_sdiff_insert,Finset.prod_const,h]
  · simp only [indRep] at h hF
    simp only [indRep,Finset.disjoint_singleton_left,Finset.insert_sdiff_insert,Finset.prod_const,h,not_false_eq_true,
      Finset.filter_true_of_mem, if_false] 
    rw [hF]
    change (∑ _a : Unit, 1*p*(1-c)⁻¹ ^ (G.neighborFinset s.endpoint \ deleted (indRep G o) s.moves).card) = _
    simp
    left
    rfl


theorem solution {V : Type} [Fintype V] (G : SimpleGraph V) (o : NeighborOrders G)
    (d : ℕ) (hd : 1 ≤ d) (hG : ∀ v, G.degree v ≤ d)
    (p c : ℝ) (hp : 0 ≤ p) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hbulk : p * ((1-c)⁻¹)^(d-1) ≤ c)
    (hroot : p * ((1-c)⁻¹)^d < 1) :
    IsMemCertificate (indRep G o) 1 (fun _ => p)
      (fun s => if s.moves = [] then p*((1-c)⁻¹)^d else c) := by
  classical
  let r := p*((1-c)⁻¹)^d
  let A := (1-c)⁻¹
  have hA : 1 ≤ A := by
    dsimp [A]
    apply (one_le_inv₀ (by linarith)).2
    linarith
  have hr0 : 0 ≤ r := mul_nonneg hp (pow_nonneg (by linarith) _)
  have hpow (k m : ℕ) (hkm : k ≤ m) : A^k ≤ A^m := pow_le_pow_right₀ hA hkm
  intro s hs
  by_cases hz : s.moves = []
  · have hbound : (G.neighborFinset s.endpoint \ deleted (indRep G o) s.moves).card ≤ d := by
      calc
        _ ≤ (G.neighborFinset s.endpoint).card := Finset.card_le_card Finset.sdiff_subset
        _ = G.degree s.endpoint := SimpleGraph.card_neighborFinset_eq_degree _ _
        _ ≤ d := hG _
    refine ⟨?_,?_,?_⟩
    · simp only [hz,if_true]
      exact hr0
    · simp only [hz,if_true]
      exact hroot
    · rw [row G o p c r s]
      simp only [hz,if_true]
      split_ifs with hdel
      · exact hr0
      · exact mul_le_mul_of_nonneg_left (hpow _ _ (by simpa [hz] using hbound)) hp
  · have hlen : s.moves.length = 1 := by
      have hh : s.moves.length ≤ 1 := hs.2
      have hp' : 0 < s.moves.length := List.length_pos_iff.mpr hz
      omega
    obtain ⟨v,hv,hdel⟩ := parent G o s hs.1 hlen
    have hsub : G.neighborFinset s.endpoint \ deleted (indRep G o) s.moves ⊂ G.neighborFinset s.endpoint := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.sdiff_subset,?_⟩
      intro heq
      have hv' : v ∈ G.neighborFinset s.endpoint \ deleted (indRep G o) s.moves := by rw [heq]; exact hv
      exact (Finset.mem_sdiff.mp hv').2 hdel
    have hcard : (G.neighborFinset s.endpoint \ deleted (indRep G o) s.moves).card <
        (G.neighborFinset s.endpoint).card := Finset.card_lt_card hsub
    have hbound : (G.neighborFinset s.endpoint \ deleted (indRep G o) s.moves).card ≤ d-1 := by
      have := hG s.endpoint
      rw [← SimpleGraph.card_neighborFinset_eq_degree] at this
      omega
    refine ⟨?_,?_,?_⟩
    · simpa [hz] using hc0
    · simpa [hz] using hc1
    · rw [row G o p c r s]
      simp only [hz,if_false]
      split_ifs with hdel'
      · exact hc0
      · exact (mul_le_mul_of_nonneg_left (hpow _ _ hbound) hp).trans hbulk

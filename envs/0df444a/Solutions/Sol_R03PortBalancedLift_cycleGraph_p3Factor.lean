-- Prove2me | solution 1 for R03PortBalancedLift.cycleGraph_p3Factor
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T01:52:21.119257+00:00
-- url     : https://prove2.me/submissions/9370a9bf-88d1-490e-a261-e33fbae4fbd5

import Mathlib
import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_2164cbfb81_sp05_port_balanced_quotient_lift_formalization_v

namespace R03PortBalancedLift

open CubicP3Partition

universe u v

variable {P : Type u} {V : Type v} [Fintype P] [Fintype V]

noncomputable section
open scoped Classical

lemma contractedRelation_symm (G : SimpleGraph V)
    (pair : (P × Fin 2) ≃ V) {p q : P} {i j : Fin 2} :
    contractedRelation G pair p i q j ↔
      contractedRelation G pair q j p i := by
  constructor
  · intro h
    exact ⟨h.1.symm, (G.adj_comm _ _).mp h.2⟩
  · intro h
    exact ⟨h.1.symm, (G.adj_comm _ _).mp h.2⟩

lemma contractedRelation_no_quotient_loop (G : SimpleGraph V)
    (pair : (P × Fin 2) ≃ V) (p : P) (i j : Fin 2) :
    ¬ contractedRelation G pair p i p j := by
  intro h
  exact h.1 rfl

lemma portFlip_zero : portFlip (0 : Fin 2) = 1 := by simp [portFlip]
lemma portFlip_one : portFlip (1 : Fin 2) = 0 := by simp [portFlip]

lemma portFlip_ne (p : Fin 2) : portFlip p ≠ p := by
  fin_cases p <;> simp [portFlip]

lemma portFlip_injective : Function.Injective portFlip := by
  intro p q hpq
  fin_cases p <;> fin_cases q <;> simp [portFlip] at hpq ⊢

lemma portFlip_eq_iff {p q : Fin 2} :
    portFlip p = q ↔ p ≠ q := by
  fin_cases p <;> fin_cases q <;> simp [portFlip]

lemma portFlip_portFlip (p : Fin 2) : portFlip (portFlip p) = p := by
  fin_cases p <;> simp [portFlip]

lemma pairingGraph_adj_iff (pair : (P × Fin 2) ≃ V)
    (p : P) (b : Fin 2) (w : V) :
    (pairingGraph pair).Adj (pair (p, b)) w ↔
      w = pair (p, portFlip b) := by
  fin_cases b
  · constructor
    · rintro ⟨q, h | h⟩
      · have hp := pair.injective h.1
        have hq : p = q := congrArg Prod.fst hp
        simpa [hq, portFlip] using h.2
      · have hp := pair.injective h.1
        exact False.elim (Fin.zero_ne_one (congrArg Prod.snd hp))
    · intro h
      exact ⟨p, Or.inl ⟨rfl, h⟩⟩
  · constructor
    · rintro ⟨q, h | h⟩
      · have hp := pair.injective h.1
        exact False.elim (Fin.zero_ne_one (congrArg Prod.snd hp).symm)
      · have hp := pair.injective h.1
        have hq : p = q := congrArg Prod.fst hp
        simpa [hq, portFlip] using h.2
    · intro h
      exact ⟨p, Or.inr ⟨rfl, h⟩⟩

lemma pairingGraph_degree (pair : (P × Fin 2) ≃ V)
    (p : P) (b : Fin 2) :
    degree (pairingGraph pair) (pair (p, b)) = 1 := by
  let e : {w : V // (pairingGraph pair).Adj (pair (p, b)) w} ≃ Fin 1 :=
    {
      toFun := fun _ => 0
      invFun := fun _ =>
        ⟨pair (p, portFlip b), (pairingGraph_adj_iff pair p b _).2 rfl⟩
      left_inv := by
        intro w
        apply Subtype.ext
        exact (pairingGraph_adj_iff pair p b w.1).mp w.2 |>.symm
      right_inv := by
        intro x
        fin_cases x
        rfl
    }
  change Nat.card {w : V // (pairingGraph pair).Adj (pair (p, b)) w} = 1
  rw [Nat.card_congr e]
  simp

lemma pairingGraph_perfectMatching
    (G : SimpleGraph V) (pair : (P × Fin 2) ≃ V)
    (pair_edge : ∀ p, G.Adj (pair (p, 0)) (pair (p, 1))) :
    PerfectMatching G (pairingGraph pair) := by
  constructor
  · intro u v huv
    rcases huv with ⟨p, h | h⟩
    · simpa [h.1, h.2] using pair_edge p
    · simpa [h.1, h.2] using (G.adj_comm _ _).mp (pair_edge p)
  · intro v
    obtain ⟨⟨p, b⟩, rfl⟩ := pair.surjective v
    exact pairingGraph_degree pair p b

lemma pairingGraph_no_loops (pair : (P × Fin 2) ≃ V) (v : V) :
    ¬ (pairingGraph pair).Adj v v := (pairingGraph pair).loopless.irrefl v

lemma mate_mem_neighborFinset
    (G : SimpleGraph V) (pair : (P × Fin 2) ≃ V)
    (pair_edge : ∀ p, G.Adj (pair (p, 0)) (pair (p, 1)))
    (p : P) (b : Fin 2) :
    pair (p, portFlip b) ∈ G.neighborFinset (pair (p, b)) := by
  fin_cases b
  · exact (G.mem_neighborFinset _ _).2 (pair_edge p)
  · exact (G.mem_neighborFinset _ _).2 ((G.adj_comm _ _).mp (pair_edge p))

lemma nonmatchingNeighborFinset_card
    (G : SimpleGraph V) (hG : CubicP3Partition.Cubic G)
    (pair : (P × Fin 2) ≃ V)
    (pair_edge : ∀ p, G.Adj (pair (p, 0)) (pair (p, 1)))
    (p : P) (b : Fin 2) :
    (nonmatchingNeighborFinset G pair p b).card = 2 := by
  have he : degree G (pair (p, b)) = G.degree (pair (p, b)) := by
    unfold degree
    rw [Nat.card_eq_fintype_card]
    exact G.card_neighborSet_eq_degree (pair (p, b))
  have hcard : (G.neighborFinset (pair (p, b))).card = 3 := by
    rw [G.card_neighborFinset_eq_degree]
    rw [← he]
    exact hG (pair (p, b))
  rw [nonmatchingNeighborFinset,
    Finset.card_erase_of_mem (mate_mem_neighborFinset G pair pair_edge p b)]
  omega

lemma contractedPortNeighborFinset_card
    (G : SimpleGraph V) (hG : CubicP3Partition.Cubic G)
    (pair : (P × Fin 2) ≃ V)
    (pair_edge : ∀ p, G.Adj (pair (p, 0)) (pair (p, 1)))
    (p : P) (b : Fin 2) :
    (contractedPortNeighborFinset G pair p b).card = 2 := by
  let A := contractedPortNeighborFinset G pair p b
  let B := nonmatchingNeighborFinset G pair p b
  have hB_adj : ∀ w : B, G.Adj (pair (p, b)) w.1 := by
    intro w
    exact (G.mem_neighborFinset _ _).1 ((Finset.mem_erase.mp w.2).2)
  have hB_ne : ∀ w : B, w.1 ≠ pair (p, portFlip b) := by
    intro w
    exact (Finset.mem_erase.mp w.2).1
  let e : A ≃ B :=
    {
      toFun := fun x =>
        ⟨pair x.1, by
          have hx : contractedRelation G pair p b x.1.1 x.1.2 := by
            simpa [A, contractedPortNeighborFinset] using x.2
          apply Finset.mem_erase.mpr
          constructor
          · intro h
            exact hx.1 (congrArg Prod.fst (pair.injective h)).symm
          · exact (G.mem_neighborFinset _ _).2 hx.2⟩
      invFun := fun w =>
        let x := pair.symm w.1
        ⟨x, by
          simp only [A, contractedPortNeighborFinset, Finset.mem_filter,
            Finset.mem_univ, true_and]
          have hxpair : pair x = w.1 := pair.apply_symm_apply w.1
          have hne : x.1 ≠ p := by
            intro hxp
            have hbadj := hB_adj w
            have hbne := hB_ne w
            rw [← hxpair] at hbadj hbne
            rcases x with ⟨q, j⟩
            change q = p at hxp
            subst q
            fin_cases b <;> fin_cases j
            · exact (G.loopless.irrefl _ hbadj)
            · exact hbne rfl
            · exact hbne rfl
            · exact (G.loopless.irrefl _ hbadj)
          exact ⟨hne.symm, by simpa [hxpair] using hB_adj w⟩⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact pair.left_inv x.1
      right_inv := by
        intro w
        apply Subtype.ext
        exact pair.apply_symm_apply w.1
    }
  have hcard : A.card = B.card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr e
  calc
    (contractedPortNeighborFinset G pair p b).card = A.card := rfl
    _ = B.card := hcard
    _ = 2 := nonmatchingNeighborFinset_card G hG pair pair_edge p b

lemma contractedHalfEdgeFinset_card
    (G : SimpleGraph V) (hG : CubicP3Partition.Cubic G)
    (pair : (P × Fin 2) ≃ V)
    (pair_edge : ∀ p, G.Adj (pair (p, 0)) (pair (p, 1)))
    (p : P) :
    (contractedHalfEdgeFinset G pair p).card = 4 := by
  rw [contractedHalfEdgeFinset, Finset.card_sigma]
  have h0 := contractedPortNeighborFinset_card G hG pair pair_edge p 0
  have h1 := contractedPortNeighborFinset_card G hG pair pair_edge p 1
  norm_num [h0, h1]

lemma allContractedHalfEdgeFinset_card
    (G : SimpleGraph V) (hG : CubicP3Partition.Cubic G)
    (pair : (P × Fin 2) ≃ V)
    (pair_edge : ∀ p, G.Adj (pair (p, 0)) (pair (p, 1))) :
    (allContractedHalfEdgeFinset G pair).card = 4 * Fintype.card P := by
  rw [allContractedHalfEdgeFinset, Finset.card_sigma]
  simp_rw [contractedHalfEdgeFinset_card G hG pair pair_edge]
  simp [Fintype.card_fin, Nat.mul_comm]

lemma reverseContractedHalfEdge_involutive (z : Σ p : P, Σ b : Fin 2, P × Fin 2) :
    reverseContractedHalfEdge (reverseContractedHalfEdge z) = z := by
  rcases z with ⟨p, ⟨b, ⟨q, j⟩⟩⟩
  rfl

lemma mem_allContractedHalfEdgeFinset_iff
    (G : SimpleGraph V) (pair : (P × Fin 2) ≃ V)
    {p q : P} {b j : Fin 2} :
    (⟨p, ⟨b, ⟨q, j⟩⟩⟩ : Σ p : P, Σ b : Fin 2, P × Fin 2) ∈
      allContractedHalfEdgeFinset G pair ↔
      contractedRelation G pair p b q j := by
  simp [allContractedHalfEdgeFinset, contractedHalfEdgeFinset,
    contractedPortNeighborFinset]

lemma reverse_mem_allContractedHalfEdgeFinset
    (G : SimpleGraph V) (pair : (P × Fin 2) ≃ V)
    (z : Σ p : P, Σ b : Fin 2, P × Fin 2) :
    z ∈ allContractedHalfEdgeFinset G pair →
      reverseContractedHalfEdge z ∈ allContractedHalfEdgeFinset G pair := by
  rcases z with ⟨p, ⟨b, ⟨q, j⟩⟩⟩
  intro hz
  have hrel : contractedRelation G pair p b q j :=
    (mem_allContractedHalfEdgeFinset_iff G pair).1 hz
  exact (mem_allContractedHalfEdgeFinset_iff G pair).2
    ((contractedRelation_symm G pair).1 hrel)

/-- The neighbor finset of the relative matching complement is the ambient
neighbor finset with the matching neighbor removed by an exact predicate. -/
lemma matchingComplement_neighborFinset_eq_filter
    (G M : SimpleGraph V) (v : V) :
    (CubicP3Partition.matchingComplement G M).neighborFinset v =
      (G.neighborFinset v).filter (fun w => ¬ M.Adj v w) := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.inf_adj,
    SimpleGraph.compl_adj, Finset.mem_filter]
  constructor
  · intro h
    exact ⟨h.1, h.2.2⟩
  · rintro ⟨hG, hM⟩
    have hne : v ≠ w := by
      intro h
      exact G.loopless.irrefl w (h ▸ hG)
    exact ⟨hG, hne, hM⟩

lemma matchingComplement_degree_two
    (G M : SimpleGraph V) (hG : CubicP3Partition.Cubic G)
    (hM : CubicP3Partition.PerfectMatching G M) (v : V) :
    CubicP3Partition.degree (CubicP3Partition.matchingComplement G M) v = 2 := by
  have hdeg (H : SimpleGraph V) :
      CubicP3Partition.degree H v = H.degree v := by
    unfold CubicP3Partition.degree
    rw [Nat.card_eq_fintype_card]
    exact H.card_neighborSet_eq_degree v
  have hGcard : (G.neighborFinset v).card = 3 := by
    rw [G.card_neighborFinset_eq_degree]
    rw [← hdeg G]
    exact hG v
  have hMcard : (M.neighborFinset v).card = 1 := by
    rw [M.card_neighborFinset_eq_degree]
    rw [← hdeg M]
    exact hM.2 v
  have hMsubset : M.neighborFinset v ⊆ G.neighborFinset v := by
    intro w hw
    exact (G.mem_neighborFinset _ _).2 (hM.1 ((M.mem_neighborFinset _ _).1 hw))
  have hfilterM :
      (G.neighborFinset v).filter (fun w => M.Adj v w) =
        M.neighborFinset v := by
    ext w
    simp only [Finset.mem_filter]
    constructor
    · intro h
      exact (M.mem_neighborFinset _ _).2 h.2
    · intro h
      exact ⟨hMsubset h, (M.mem_neighborFinset _ _).1 h⟩
  have hnotcard :
      ((G.neighborFinset v).filter (fun w => ¬ M.Adj v w)).card = 2 := by
    have hsum := Finset.card_filter_add_card_filter_not
      (s := G.neighborFinset v) (fun w => M.Adj v w)
    rw [hfilterM, hMcard, hGcard] at hsum
    omega
  calc
    CubicP3Partition.degree (CubicP3Partition.matchingComplement G M) v =
        (CubicP3Partition.matchingComplement G M).degree v := hdeg _
    _ = ((CubicP3Partition.matchingComplement G M).neighborFinset v).card :=
      (CubicP3Partition.matchingComplement G M).card_neighborFinset_eq_degree v |>.symm
    _ = ((G.neighborFinset v).filter (fun w => ¬ M.Adj v w)).card := by
      rw [matchingComplement_neighborFinset_eq_filter]
    _ = 2 := hnotcard

lemma matchingComplement_twoFactor
    (G M : SimpleGraph V) (hG : CubicP3Partition.Cubic G)
    (hM : CubicP3Partition.PerfectMatching G M) :
    CubicP3Partition.TwoFactor G
      (CubicP3Partition.matchingComplement G M) := by
  constructor
  · exact inf_le_left
  · intro v
    exact matchingComplement_degree_two G M hG hM v

lemma port_pair_card (b : Nat) :
    Fintype.card (Fin b × Fin 2) = 2 * b := by
  simp [Fintype.card_prod, Nat.mul_comm]

end
end R03PortBalancedLift

open R03PortBalancedLift
open CubicP3Partition
universe u v
variable {P : Type u} {V : Type v} [Fintype P] [Fintype V]
open scoped Classical
theorem solution (k : Nat) :
    Nonempty (CubicP3Partition.P3Factor
      (SimpleGraph.cycleGraph (3 * k))) := by
  cases k with
  | zero =>
      let place : (Fin 0 × Fin 3) ≃ Fin (3 * 0) := cycleBlockPlace 0
      exact ⟨{
        blockCount := 0
        place := place
        edge01 := by intro i; exact i.elim0
        edge12 := by intro i; exact i.elim0
      }⟩
  | succ k =>
      let place : (Fin (k + 1) × Fin 3) ≃ Fin (3 * (k + 1)) :=
        cycleBlockPlace (k + 1)
      exact ⟨{
        blockCount := k + 1
        place := place
        edge01 := by
          intro i
          rw [SimpleGraph.cycleGraph_adj']
          right
          rw [Fin.sub_val_of_le (by
            simp [place, cycleBlockPlace, finProdFinEquiv])]
          simp [place, cycleBlockPlace, finProdFinEquiv]
        edge12 := by
          intro i
          rw [SimpleGraph.cycleGraph_adj']
          right
          rw [Fin.sub_val_of_le (by
            simp [place, cycleBlockPlace, finProdFinEquiv])]
          simp [place, cycleBlockPlace, finProdFinEquiv] <;> omega
      }⟩

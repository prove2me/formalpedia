-- Prove2me | solution 1 for SimpleGraph.goodman_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:42:54.563656+00:00
-- url     : https://prove2.me/submissions/54c3919d-56ff-47f7-bbe3-ac06c6812d9e

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Zify
public import Definitions.Def_GoodmanSupersaturation_Goodman
public import Theorems.Thm_SimpleGraph_degreeWithin_univ
public import Theorems.Thm_SimpleGraph_cliqueCountIn_univ
attribute [local simp] SimpleGraph.degreeWithin_univ
attribute [local simp] SimpleGraph.cliqueCountIn_univ
section
@[expose] public section
open Finset
namespace SimpleGraph
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
private theorem card_distinctTriples' (s : Finset V) :
    #(distinctTriples s) = #s * ((#s - 1) * (#s - 1) - (#s - 1)) := by
  rw [distinctTriples, card_filter, sum_product, ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun x hx => ?_
  rw [← card_erase_of_mem hx, ← offDiag_card, ← card_filter]
  congr 1
  ext ⟨y, z⟩
  simp only [mem_filter, mem_product, mem_offDiag, mem_erase]
  constructor
  · rintro ⟨⟨hy, hz⟩, hxy, hxz, hyz⟩
    exact ⟨⟨Ne.symm hxy, hy⟩, ⟨Ne.symm hxz, hz⟩, hyz⟩
  · rintro ⟨⟨hxy, hy⟩, ⟨hxz, hz⟩, hyz⟩
    exact ⟨⟨hy, hz⟩, Ne.symm hxy, Ne.symm hxz, hyz⟩
private theorem card_distinctTriples (S : Finset V) :
    #(distinctTriples S) = 6 * (#S).choose 3 := by
  rw [card_distinctTriples', show 6 = Nat.factorial 3 from rfl,
    ← Nat.descFactorial_eq_factorial_mul_choose, ← Nat.mul_sub_one]
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero, mul_one,
    show #S - 1 - 1 = #S - 2 by omega]
  ring
private theorem mem_distinctTriples {S : Finset V} {x : V × V × V} :
    x ∈ distinctTriples S ↔
      (x.1 ∈ S ∧ x.2.1 ∈ S ∧ x.2.2 ∈ S) ∧ x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2 ∧ x.2.1 ≠ x.2.2 := by
  simp [distinctTriples]
private theorem card_triangleTriples (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) :
    #(triangleTriples H S) = 6 * H.cliqueCountIn S 3 := by
  rw [cliqueCountIn, card_eq_sum_card_fiberwise
    (f := fun x : V × V × V => ({x.1, x.2.1, x.2.2} : Finset V))
    (t := (S.powersetCard 3).filter fun T : Finset V => H.IsClique (T : Set V))]
  · rw [mul_comm, ← smul_eq_mul, ← sum_const]
    refine sum_congr rfl fun s hs => ?_
    rw [mem_filter, mem_powersetCard] at hs
    obtain ⟨⟨hsS, hs3⟩, hcl⟩ := hs
    have h6 := card_distinctTriples' s
    rw [hs3, show 3 * ((3 - 1) * (3 - 1) - (3 - 1)) = 6 from rfl] at h6
    rw [← h6]
    congr 1
    ext ⟨x, y, z⟩
    simp only [triangleTriples, distinctTriples, mem_filter, mem_product]
    constructor
    · rintro ⟨⟨-, hxy, hxz, hyz⟩, rfl⟩
      exact ⟨⟨by simp, by simp, by simp⟩, hxy.ne, hxz.ne, hyz.ne⟩
    · rintro ⟨⟨hx, hy, hz⟩, hxy, hxz, hyz⟩
      refine ⟨⟨⟨hsS hx, hsS hy, hsS hz⟩, hcl hx hy hxy, hcl hx hz hxz, hcl hy hz hyz⟩, ?_⟩
      refine eq_of_subset_of_card_le (by simp [insert_subset_iff, hx, hy, hz]) ?_
      rw [hs3, card_insert_of_notMem (by simp [hxy, hxz]), card_pair hyz]
  · intro x hx
    have hx := mem_coe.mp hx
    simp only [triangleTriples, mem_filter, mem_product] at hx
    obtain ⟨⟨h1, h2, h3⟩, a, b, c⟩ := hx
    change {x.1, x.2.1, x.2.2} ∈ (((S.powersetCard 3).filter
      fun T : Finset V => H.IsClique (T : Set V) : Finset (Finset V)) : Set (Finset V))
    rw [mem_coe, mem_filter, mem_powersetCard]
    have h := is3Clique_triple_iff.mpr ⟨a, b, c⟩
    exact ⟨⟨by simp [insert_subset_iff, h1, h2, h3], h.card_eq⟩, by
      simpa using h.isClique⟩
private theorem card_mixedTriples (S : Finset V) :
    #(mixedTriples G S) = ∑ v ∈ S, G.degreeWithin S v * Gᶜ.degreeWithin S v := by
  rw [mixedTriples, card_filter, sum_product]
  refine sum_congr rfl fun u _ => ?_
  rw [degreeWithin, degreeWithin, ← card_product, ← card_filter]
  congr 1
  ext ⟨v, w⟩
  simp only [mem_filter, mem_product]
  tauto
private theorem sum_distinctTriples_comp (S : Finset V) (f : V × V × V → ℕ)
    (σ τ : V × V × V → V × V × V) (hστ : ∀ x, σ (τ x) = x) (hτσ : ∀ x, τ (σ x) = x)
    (hD : ∀ x, σ x ∈ distinctTriples S ↔ x ∈ distinctTriples S) :
    ∑ x ∈ distinctTriples S, f (σ x) = ∑ x ∈ distinctTriples S, f x :=
  sum_nbij' σ τ (fun x hx => (hD x).2 hx) (fun x hx => by rw [← hD, hστ]; exact hx)
    (fun x _ => hτσ x) (fun x _ => hστ x) fun _ _ => rfl
private theorem pointwise {u v w : V} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    mixedInd G (u, v, w) + mixedInd G (u, w, v) + mixedInd G (v, u, w) + mixedInd G (v, w, u) +
      mixedInd G (w, u, v) + mixedInd G (w, v, u) + 2 * monoInd G (u, v, w) = 2 := by
  simp only [mixedInd, monoInd, compl_adj, ne_eq, huv, huw, hvw, Ne.symm huv, Ne.symm huw,
    Ne.symm hvw, not_false_eq_true, true_and, G.adj_comm v u, G.adj_comm w u, G.adj_comm w v]
  by_cases a : G.Adj u v <;> by_cases b : G.Adj u w <;> by_cases c : G.Adj v w <;> simp [a, b, c]
section Fintype
variable [Fintype V]
end Fintype
end SimpleGraph
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution (S : Finset V) :
    2 * (G.cliqueCountIn S 3 + Gᶜ.cliqueCountIn S 3) +
        ∑ v ∈ S, G.degreeWithin S v * Gᶜ.degreeWithin S v = 2 * (#S).choose 3 := by
  have hsum : ∑ x ∈ distinctTriples S, (mixedInd G x + mixedInd G (x.1, x.2.2, x.2.1) +
      mixedInd G (x.2.1, x.1, x.2.2) + mixedInd G (x.2.1, x.2.2, x.1) +
      mixedInd G (x.2.2, x.1, x.2.1) + mixedInd G (x.2.2, x.2.1, x.1) + 2 * monoInd G x) =
      ∑ _x ∈ distinctTriples S, 2 := by
    refine sum_congr rfl fun ⟨u, v, w⟩ hx => ?_
    obtain ⟨-, huv, huw, hvw⟩ := mem_distinctTriples.mp hx
    exact pointwise G huv huw hvw
  have hsub : distinctTriples S ⊆ S ×ˢ S ×ˢ S := filter_subset _ _
  -- each permuted sum is the mixed-wedge count
  have hperm : ∀ (σ τ : V × V × V → V × V × V), (∀ x, σ (τ x) = x) → (∀ x, τ (σ x) = x) →
      (∀ x, σ x ∈ distinctTriples S ↔ x ∈ distinctTriples S) →
      ∑ x ∈ distinctTriples S, mixedInd G (σ x) = #(mixedTriples G S) := by
    intro σ τ h1 h2 h3
    rw [sum_distinctTriples_comp S _ σ τ h1 h2 h3, mixedTriples, card_filter]
    refine (sum_subset hsub fun x hxS hx => ?_).trans rfl
    simp only [mixedInd, ite_eq_right_iff, one_ne_zero, imp_false, not_and]
    intro h h'
    refine hx (mem_distinctTriples.mpr ⟨by simpa [mem_product] using hxS, h.ne, h'.ne,
      fun e => ?_⟩)
    rw [compl_adj] at h'
    exact h'.2 (e ▸ h)
  have hmono : ∑ x ∈ distinctTriples S, monoInd G x =
      #(triangleTriples G S) + #(triangleTriples Gᶜ S) := by
    rw [triangleTriples, triangleTriples, card_filter, card_filter, ← sum_add_distrib]
    refine (sum_subset hsub fun x hxS hx => ?_).trans rfl
    rw [mem_distinctTriples] at hx
    have hS : x.1 ∈ S ∧ x.2.1 ∈ S ∧ x.2.2 ∈ S := by simpa [mem_product] using hxS
    have hA : ¬(G.Adj x.1 x.2.1 ∧ G.Adj x.1 x.2.2 ∧ G.Adj x.2.1 x.2.2) := fun h =>
      hx ⟨hS, h.1.ne, h.2.1.ne, h.2.2.ne⟩
    have hB : ¬(Gᶜ.Adj x.1 x.2.1 ∧ Gᶜ.Adj x.1 x.2.2 ∧ Gᶜ.Adj x.2.1 x.2.2) := fun h =>
      hx ⟨hS, h.1.ne, h.2.1.ne, h.2.2.ne⟩
    simp only [monoInd, hA, hB, ↓reduceIte, add_zero]
  have h0 : ∑ x ∈ distinctTriples S, mixedInd G x = #(mixedTriples G S) :=
    hperm id id (fun _ => rfl) (fun _ => rfl) (fun _ => Iff.rfl)
  simp only [sum_add_distrib, ← mul_sum] at hsum
  rw [h0,
    hperm (fun x => (x.1, x.2.2, x.2.1)) (fun x => (x.1, x.2.2, x.2.1)) (fun _ => rfl)
      (fun _ => rfl) (fun x => by simp only [mem_distinctTriples]; tauto),
    hperm (fun x => (x.2.1, x.1, x.2.2)) (fun x => (x.2.1, x.1, x.2.2)) (fun _ => rfl)
      (fun _ => rfl) (fun x => by simp only [mem_distinctTriples]; tauto),
    hperm (fun x => (x.2.1, x.2.2, x.1)) (fun x => (x.2.2, x.1, x.2.1)) (fun _ => rfl)
      (fun _ => rfl) (fun x => by simp only [mem_distinctTriples]; tauto),
    hperm (fun x => (x.2.2, x.1, x.2.1)) (fun x => (x.2.1, x.2.2, x.1)) (fun _ => rfl)
      (fun _ => rfl) (fun x => by simp only [mem_distinctTriples]; tauto),
    hperm (fun x => (x.2.2, x.2.1, x.1)) (fun x => (x.2.2, x.2.1, x.1)) (fun _ => rfl)
      (fun _ => rfl) (fun x => by simp only [mem_distinctTriples]; tauto),
    hmono, sum_const, smul_eq_mul, card_distinctTriples, card_triangleTriples,
    card_triangleTriples, card_mixedTriples] at hsum
  linarith
end SimpleGraph

-- Prove2me | solution 1 for SimpleGraph.exists_monochromatic_book
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:59:51.30275+00:00
-- url     : https://prove2.me/submissions/d52c48a3-63e6-413e-9397-9d6785c9a8ec

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
public import Theorems.Thm_SimpleGraph_degree_add_degree_compl
public import Theorems.Thm_SimpleGraph_goodman_bound
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
section Fintype
variable [Fintype V]
omit [DecidableEq V] in
/-- Codegrees as filters. -/
private theorem card_commonNeighbors_eq_filter (H : SimpleGraph V) [DecidableRel H.Adj] (u v : V) :
    Fintype.card (H.commonNeighbors u v) = #{w | H.Adj u w ∧ H.Adj v w} := by
  rw [← Set.toFinset_card]
  congr 1
  ext w
  simp [mem_commonNeighbors]
private theorem sum_codegree_eq (H : SimpleGraph V) [DecidableRel H.Adj] :
    ∑ u, ∑ v ∈ H.neighborFinset u, Fintype.card (H.commonNeighbors u v) =
      6 * #(H.cliqueFinset 3) := by
  rw [← cliqueCountIn_univ, ← card_triangleTriples]
  simp only [triangleTriples, card_filter, sum_product, card_commonNeighbors_eq_filter]
  refine sum_congr rfl fun u _ => ?_
  rw [neighborFinset_eq_filter, sum_filter]
  refine sum_congr rfl fun v _ => ?_
  split_ifs with h <;> simp [h]
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
variable [Fintype V]
namespace SimpleGraph
theorem _root_.solution {q : ℕ} (hq : 4 * q + 2 ≤ Fintype.card V) :
    ∃ u v, (G.Adj u v ∧ q ≤ Fintype.card (G.commonNeighbors u v)) ∨
      (Gᶜ.Adj u v ∧ q ≤ Fintype.card (Gᶜ.commonNeighbors u v)) := by
  have hcard : 2 ≤ Fintype.card V := by omega
  obtain ⟨u, v, huv⟩ := Fintype.exists_pair_of_one_lt_card hcard
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · by_cases h : G.Adj u v
    · exact ⟨u, v, .inl ⟨h, Nat.zero_le _⟩⟩
    · exact ⟨u, v, .inr ⟨(compl_adj G u v).mpr ⟨huv, h⟩, Nat.zero_le _⟩⟩
  by_contra hne
  simp only [not_exists, not_or, not_and, not_le] at hne
  have hle : ∀ H : SimpleGraph V, [DecidableRel H.Adj] →
      (∀ u v, H.Adj u v → Fintype.card (H.commonNeighbors u v) < q) →
      6 * #(H.cliqueFinset 3) ≤ (q - 1) * ∑ u, H.degree u := by
    intro H _ hH
    rw [← sum_codegree_eq, mul_sum]
    refine sum_le_sum fun u _ => ?_
    rw [← card_neighborFinset_eq_degree, mul_comm, ← smul_eq_mul, ← sum_const]
    exact sum_le_sum fun v hv => Nat.le_sub_one_of_lt (hH u v ((mem_neighborFinset _ _ _).mp hv))
  have h1 := hle G fun u v h => (hne u v).1 h
  have h2 := hle Gᶜ fun u v h => (hne u v).2 h
  have hdeg : ∑ u, G.degree u + ∑ u, Gᶜ.degree u = Fintype.card V * (Fintype.card V - 1) := by
    rw [← sum_add_distrib, sum_congr rfl fun v _ => degree_add_degree_compl G v, sum_const,
      card_univ, smul_eq_mul]
  have hg := goodman_bound G
  set n := Fintype.card V
  set T := #(G.cliqueFinset 3) + #(Gᶜ.cliqueFinset 3)
  have hsum : 6 * T ≤ (q - 1) * (n * (n - 1)) := by
    rw [← hdeg, mul_add]
    simp only [mul_add]
    omega
  have h5 : n * (n - 1) * (4 * q - 3) ≤ n * (n - 1) * (n - 5) :=
    Nat.mul_le_mul_left _ (by omega)
  have hpos : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
  have : n * (n - 1) * (4 * q - 3) ≤ n * (n - 1) * (4 * (q - 1)) := by
    calc n * (n - 1) * (4 * q - 3) ≤ 24 * T := h5.trans hg
      _ = 4 * (6 * T) := by ring
      _ ≤ 4 * ((q - 1) * (n * (n - 1))) := Nat.mul_le_mul_left 4 hsum
      _ = n * (n - 1) * (4 * (q - 1)) := by ring
  have := Nat.le_of_mul_le_mul_left this hpos
  omega
end SimpleGraph

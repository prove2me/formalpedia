-- Prove2me | solution 1 for OpenMath.WOWII19.bound_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:39:44.909504+00:00
-- url     : https://prove2.me/submissions/bdfc636a-d997-4aeb-bc9a-c907a3960f75

module
public import Definitions.Def_OpenMath_Common
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_OpenMath_WOWII19
public import Theorems.Thm_OpenMath_WOWII19_le_indepIn
public import Theorems.Thm_OpenMath_WOWII19_sum_indepIn_le_b
public import Theorems.Thm_OpenMath_WOWII19_one_le_indepIn_layer
public import Theorems.Thm_OpenMath_WOWII19_indepNeighborsCard_le_indepIn_layer_one
public import Theorems.Thm_OpenMath_dist_getVert_of_geodesic
public import Theorems.Thm_OpenMath_dist_le_ecc


set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
open OpenMath OpenMath.WOWII19
open SimpleGraph Finset OpenMath
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α}
namespace OpenMath.WOWII19
theorem _root_.solution (h : G.Connected) (v x y : α) (D : ℕ) (hxy : G.dist x y = D)
    (hav : G.dist v x ≤ G.dist v y) (he : 1 ≤ ecc G v) :
    indepNeighborsCard G v + D ≤ largestInducedBipartiteSubgraphSize G + 1 := by
  set a := G.dist v x with ha
  set c := G.dist v y with hc
  set e := ecc G v with he_def
  have hae : a ≤ e := dist_le_ecc h v x
  have hce : c ≤ e := dist_le_ecc h v y
  have hacD : D ≤ a + c := by
    have := h.dist_triangle (u := x) (v := v) (w := y)
    rw [dist_comm (u := x) (v := v)] at this
    omega
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist v x
  obtain ⟨q, hq⟩ := h.exists_walk_length_eq_dist v y
  -- first good layer
  set i0 := max 2 ((a + c + 3 - D) / 2) with hi0
  -- in every layer `i ∈ [i0, a]` the geodesic vertices `x_i, y_i` are independent
  have hgood : ∀ i ∈ Icc i0 a, 2 ≤ indepIn G (layer G v i) := by
    intro i hi
    rw [mem_Icc] at hi
    have hia : i ≤ p.length := by omega
    have hic : i ≤ q.length := by omega
    obtain ⟨hpx1, hpx2⟩ := dist_getVert_of_geodesic h p hp hia
    obtain ⟨hqy1, hqy2⟩ := dist_getVert_of_geodesic h q hq hic
    have t1 := h.dist_triangle (u := x) (v := p.getVert i) (w := y)
    have t2 := h.dist_triangle (u := p.getVert i) (v := q.getVert i) (w := y)
    have t3 : G.dist x (p.getVert i) = G.dist (p.getVert i) x := dist_comm
    have hfar : 2 ≤ G.dist (p.getVert i) (q.getVert i) := by
      have : a + c + 2 ≤ D + 2 * i := by omega
      omega
    have hne : p.getVert i ≠ q.getVert i := by
      intro heq
      rw [heq, dist_self] at hfar
      omega
    have hnadj : ¬ G.Adj (p.getVert i) (q.getVert i) := by
      intro hadj
      rw [dist_eq_one_iff_adj.mpr hadj] at hfar
      omega
    have := le_indepIn (G := G) (s := {p.getVert i, q.getVert i}) (T := layer G v i)
      (by
        intro z hz
        simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl <;> simp [layer, hpx1, hqy1])
      (by
        rw [coe_pair]
        exact Set.pairwise_pair.mpr fun _ => ⟨hnadj, fun h' => hnadj h'.symm⟩)
    rwa [card_pair hne] at this
  -- sum over layers
  refine le_trans ?_ (Nat.add_le_add_right (sum_indepIn_le_b G v e) 1)
  obtain ⟨k, hk⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  rw [hk, sum_range_succ', sum_range_succ']
  have h0 : 1 ≤ indepIn G (layer G v 0) := one_le_indepIn_layer h v (by omega)
  have h1 := indepNeighborsCard_le_indepIn_layer_one (G := G) v
  -- each remaining layer `j + 2` (for `j < k`) contributes `1`, plus `1` if it is good
  have hrest : ∑ j ∈ range k, (1 + if j + 2 ∈ Icc i0 a then 1 else 0)
      ≤ ∑ j ∈ range k, indepIn G (layer G v (j + 1 + 1)) := by
    apply sum_le_sum
    intro j hj
    rw [mem_range] at hj
    split_ifs with hg
    · exact hgood (j + 2) hg
    · exact one_le_indepIn_layer h v (by omega)
  have hcount : a + 1 - i0 ≤ ∑ j ∈ range k, (if j + 2 ∈ Icc i0 a then 1 else 0) := by
    rw [sum_boole, Nat.cast_id, ← Nat.card_Icc]
    apply card_le_card_of_injOn (fun i => i - 2)
    · intro i hi
      simp only [coe_Icc, Set.mem_Icc] at hi
      simp only [coe_filter, mem_range, mem_Icc, Set.mem_ofPred_eq]
      have : 2 ≤ i0 := le_max_left _ _
      refine ⟨by omega, by omega, by omega⟩
    · intro i hi j hj hij
      simp only [coe_Icc, Set.mem_Icc] at hi hj
      have : 2 ≤ i0 := le_max_left _ _
      simp only at hij
      omega
  rw [sum_add_distrib] at hrest
  simp only [sum_const, card_range, smul_eq_mul, mul_one] at hrest
  simp only [zero_add] at h1 h0 ⊢
  omega
end OpenMath.WOWII19

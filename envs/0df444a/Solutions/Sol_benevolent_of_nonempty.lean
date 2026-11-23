-- Prove2me | solution 1 for benevolent_of_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:44:27.319773+00:00
-- url     : https://prove2.me/submissions/6f1fcc6c-f975-4f12-86f6-78f54032e914

module
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Definitions.Def_ChipFiringWithLean_Basic
public import Theorems.Thm_deg_one_chip
attribute [local simp] deg_one_chip
section
@[expose] public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
private lemma mem_principal_divisors_firing_vector (G : CFGraph) (v : G.V) :
  firing_vector G v ∈ principal_divisors G := AddSubgroup.subset_closure (Set.mem_range_self v)
open Matrix
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
open Matrix
theorem _root_.solution {G : CFGraph} (h_conn : graph_connected G) (S : Finset G.V) (h_nonempty : S.Nonempty) :
  benevolent G S := by
  by_cases h : S = Finset.univ
  · -- Case: S = G.V
    intro D
    use D
    -- Verify the first part of the conjunction
    constructor
    exact linear_equiv.refl G D
    -- Verify second part
    intro v h_neg
    rw [h]
    simp only [mem_univ]
  · -- Case: S ≠ G.V
    let h_conn' := h_conn -- Unsimplified copy for later
    dsimp only [graph_connected] at h_conn
    specialize h_conn S
    have : ∃ (v w : G.V), v ∈ S ∧ w ∉ S := by
      let v := Classical.choose h_nonempty
      have v_in_S : v ∈ S := Classical.choose_spec h_nonempty
      have : (univ \ S).Nonempty := by
        contrapose! h
        simp only [sdiff_eq_empty_iff_subset, univ_subset_iff] at h
        exact h
      let w := Classical.choose this
      have h_vw : w ∉ S := by
        have := Classical.choose_spec this
        simp only [mem_sdiff, mem_univ, true_and] at this
        exact this
      use v, w
    have h_vw := h_conn this
    rcases h_vw with ⟨v,h_v,w,h_w,h_edge⟩
    let T := insert w S
    have h_T_nonempty : T.Nonempty := by
      use w
      simp only [mem_insert, true_or, T]
    have ih := solution h_conn' T h_T_nonempty
    intro D
    specialize ih D
    rcases ih with ⟨E1, h_lequiv_1, h_eff_S⟩
    -- Now need to adjust E1 to get E
    have : ∃ E : CFDiv G, linear_equiv G E1 E ∧ (∀ v : G.V, E v < 0 → v ∈ S) := by
      let fire := firing_vector G v
      have p_f : fire ∈ principal_divisors G := mem_principal_divisors_firing_vector G v
      let k := max 0 (-(E1 w))
      let E := E1 + k • fire
      use E
      constructor
      · -- Verify linear equivalence
        unfold linear_equiv
        have h_diff : E - E1 = k • fire := by
          simp only [zsmul_eq_mul, add_sub_cancel_left, E]
        rw [h_diff]
        exact AddSubgroup.zsmul_mem _ p_f k
      · -- Verify effectiveness outside S
        intro x h_E_neg
        by_cases h_x_eq_w : x = w
        · -- Case x = w
          exfalso
          rw [h_x_eq_w] at h_E_neg
          dsimp only [Pi.add_apply, Pi.smul_apply, Int.zsmul_eq_mul, E] at h_E_neg
          contrapose! h_E_neg
          simp only [k]
          by_cases h : -(E1 w) ≥ 0
          . -- Case : E1 w nonpositive
            have : max 0 (-(E1 w)) = -(E1 w) := by
              simp only [sup_eq_right, Int.neg_nonneg]; linarith
            rw [this]
            have : E1 w + -E1 w * fire w = (-E1 w) * (fire w -1) := by ring
            rw [this]
            apply mul_nonneg h
            -- Goal: fire w -1 ≥ 0
            dsimp only [firing_vector, fire]
            have : ¬ (w = v) := by
              contrapose! h_w
              rw [← h_w] at h_v
              exact h_v
            simp only [this, ↓reduceIte, Int.sub_nonneg, Nat.one_le_cast, ge_iff_le]
            linarith [h_edge]
          . -- Case : E1 w positive
            push Not at h
            dsimp only [max, Int.neg_nonneg]
            split_ifs at * with hle
            · linarith
            · simp only [zero_mul, add_zero] at *; linarith
        . -- Case : x ≠ w
          have h_T := h_eff_S x
          by_contra! x_nin_S
          have h_xT : x ∉ T := by
            contrapose! x_nin_S with x_in_T
            dsimp only [T] at x_in_T
            simp only [mem_insert, h_x_eq_w, false_or] at x_in_T
            exact x_in_T
          specialize h_eff_S x
          contrapose! h_eff_S
          simp only [h_xT, not_false_eq_true, and_true]
          contrapose! h_E_neg with h_E1
          -- Goal: 0 ≤ E x
          dsimp only [Pi.add_apply, Pi.smul_apply, Int.zsmul_eq_mul, E]
          apply add_nonneg h_E1
          -- Goal : 0 ≤ k * fire x
          apply mul_nonneg
          -- Show 0 ≤ k
          dsimp only [k]
          simp only [le_sup_left]
          -- Show 0 ≤ fire x
          dsimp only [firing_vector, fire]
          have : ¬ (x = v) := by
            contrapose! x_nin_S with x_eq_v
            rw [x_eq_v]
            exact h_v
          simp only [this, ↓reduceIte, Nat.cast_nonneg]
    rcases this with ⟨E, h_lequiv_2, h_eff_S_final⟩
    use E
    constructor
    · -- Verify linear equivalence
      exact h_lequiv_1.trans h_lequiv_2
    · -- Verify effectiveness outside S
      exact h_eff_S_final
termination_by ((univ : Finset G.V).card - S.card)
decreasing_by
  have h_succ: (insert w S).card = S.card + 1 := by
    apply Finset.card_eq_succ.mpr
    use w, S
  rw [h_succ]
  refine Nat.sub_succ_lt_self univ.card S.card ?_
  have : (insert w S).card ≤ (univ : Finset G.V).card := by
    simpa only [card_univ] using Finset.card_le_univ (insert w S)
  linarith

-- Prove2me | solution 1 for burnin_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:48:40.954833+00:00
-- url     : https://prove2.me/submissions/3bdc3426-e6fb-46d3-8840-c824a9d38211

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Config
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
public import Theorems.Thm_num_edges_symmetric
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty



set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution {G : CFGraph} {q : G.V} {c : Config G q} (L : burn_list G c) (v : G.V) (h_pres : v ∈ L.list) (h_ne : v ≠ q): ∑ (w : G.V), burn_flow L ⟨w,v⟩ > c.chips v := by
  let h_bl := L.h_burn_list
  cases h: L.list with
  | nil =>
    rw [h] at h_bl
    dsimp only [is_burn_list] at h_bl
  | cons x rest =>
    cases h' : rest with
    | nil =>
      rw [h'] at h
      rw [h] at h_bl
      dsimp only [is_burn_list] at h_bl
      -- So x = q
      simp only [h, List.mem_cons, List.not_mem_nil, or_false] at h_pres
      rw [h_pres, ← h_bl] at h_ne
      contradiction
    | cons y rest' =>
      rw [h'] at h
      rw [h] at h_bl
      dsimp only [is_burn_list] at h_bl
      -- Need to analyze the position of v in the list
      by_cases h_vx : v = x
      . -- Case: v = x
        rw [← h_vx] at h_bl
        suffices ∑ (w : G.V), burn_flow L ⟨w,v⟩ ≥ outdeg_S G (univ \ (y :: rest').toFinset) v by
          linarith [this, h_bl.1]
        dsimp only [burn_flow]
        have ind_v : L.list.idxOf v = 0 := by
          rw [h_vx,h]
          simp only [List.idxOf_cons_self]
        simp only [ind_v]
        have h_ineq := h_bl.1
        have h_above : ∀ (x : G.V), x ∈ L.list ∧ 0 < List.idxOf x L.list ↔ x ∈ rest := by
          intro w
          rw [← h'] at h
          rw [h]
          simp only [List.mem_cons]
          have : 0 < List.idxOf w (x :: rest) ↔ 0 ≠ List.idxOf w (x :: rest) := by
            constructor
            . intro h_pos h_eq
              rw [h_eq] at h_pos
              linarith
            . intro h_neq
              simp only [ne_eq] at h_neq
              apply Nat.zero_lt_of_ne_zero
              contrapose! h_neq with h_eq_zero
              rw [h_eq_zero]
          rw [this]
          have : 0 ≠ List.idxOf w (x :: rest) ↔ w ≠ x := by
            constructor
            . intro h_neq
              contrapose! h_neq with h_eq
              rw [h_eq]
              simp only [List.idxOf_cons_self]
            . intro h_neq
              rw [List.idxOf_cons_ne _ (Ne.symm h_neq)]
              simp only [Nat.succ_eq_add_one, ne_eq, Nat.right_eq_add, Nat.add_eq_zero_iff,
                  one_ne_zero, and_false, not_false_eq_true]
          rw [this]
          constructor
          . -- Forward direction
            intro h_w
            by_contra!
            simp only [this, or_false, ne_eq, and_not_self] at h_w
          . -- Reverse direction
            intro h_w_in_rest
            simp only [h_w_in_rest, or_true, ne_eq, true_and]
            by_contra!
            rw [this] at h_w_in_rest
            have := h_bl.2.1
            rw [h_vx] at this
            rw [← h'] at this
            absurd this
            simp only [List.contains_eq_mem, h_w_in_rest, decide_true]
        simp only [h_above]
        dsimp only [outdeg_S]
        rw [← h']
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
        simp only [Nat.cast_sum, sdiff_sdiff_right_self, subset_univ, inf_of_le_right, ge_iff_le]
        have : Finset.filter (Membership.mem rest) univ = rest.toFinset := by
          ext w
          simp only [Finset.mem_filter, mem_univ, true_and, List.mem_toFinset]
        rw [this]
        apply sum_le_sum
        intro i _
        rw [num_edges_symmetric G i v]
      . -- Case: v ≠ x
        let L' := burn_list.mk (y :: rest') (h_bl.2.2)
        have h_v_in_L' : v ∈ L'.list := by
          dsimp only [L']
          rw [← h']
          rw [← h'] at h
          rw [h] at h_pres
          simp only [List.mem_cons, h_vx, false_or] at h_pres
          exact h_pres
        have h_step : ∀ (w : G.V), burn_flow L ⟨w,v⟩ = burn_flow L' ⟨w,v⟩ := by
          have h_x_nin_rest: x ∉ rest := by
            have := L.h_burn_list
            rw [h] at this
            have := this.2.1
            rw [h']
            simp only [List.contains_eq_mem, List.mem_cons, Bool.decide_or, Bool.or_eq_true,
                decide_eq_true_eq, not_or] at this
            simp only [List.mem_cons, this, or_self, not_false_eq_true]
          intro w
          dsimp only [burn_flow, L']
          rw [h]
          rw [List.idxOf_cons_ne _ (Ne.symm h_vx)]
          by_cases h_wx : w = x
          . -- Subcase: w = x
            rw [h_wx]
            have h0 : (x :: y :: rest').idxOf x = 0 := List.idxOf_cons_self
            rw [h0, if_neg (fun ⟨_, h⟩ => Nat.not_lt_zero _ h),
               if_neg (fun ⟨h_mem, _⟩ => (h' ▸ h_x_nin_rest) h_mem)]
          . -- Subcase: w ≠ x
            simp only [List.mem_cons, h_wx, false_or]
            rw [List.idxOf_cons_ne (y :: rest') (Ne.symm h_wx)]
            simp only [Nat.succ_lt_succ_iff]
        simp only [h_step]
        have h_ind := solution L' v h_v_in_L' h_ne
        exact h_ind
termination_by L.list.length
decreasing_by
  rw [h,h']
  simp only [List.length_cons, lt_add_iff_pos_right, Order.lt_one_iff]

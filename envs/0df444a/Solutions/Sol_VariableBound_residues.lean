-- Prove2me | solution 1 for VariableBound.residues
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T22:59:49.968528+00:00
-- url     : https://prove2.me/submissions/40058532-f364-4efb-95e3-a1da421fd849

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.List.GetD
import Definitions.Def_VariableBound_StepParity
import Theorems.Thm_ClauseBound_ParityChecks_StepOne_product
set_option autoImplicit false
section
section
open VariableBound
open Finset ParityChecks AppVariables StepParity

namespace VariableBound.StepParity

open Finset ParityChecks AppVariables

variable {X E : Type} [DecidableEq E]

/-- The product over the checks of a list is the product over their numbers `j : Fin r`. -/
theorem allEven_eq_fin (V : X → Finset E) (L : List (Finset E)) (ξ : X) :
    allEven V L ξ = ∏ j : Fin L.length, ev #(L.getD j ∅ ∩ V ξ) := by
  rw [allEven, ← Fin.prod_univ_fun_getElem]
  exact prod_congr rfl fun j _ => by rw [List.getD_eq_getElem _ _ j.isLt]

/-- The product over the checks is also a product over their numbers in `range L.length`. -/
theorem allEven_eq_range (V : X → Finset E) (L : List (Finset E)) (ξ : X) :
    allEven V L ξ = ∏ j ∈ range L.length, ev #(L.getD j ∅ ∩ V ξ) := by
  rw [allEven_eq_fin, prod_range fun j => ev #(L.getD j ∅ ∩ V ξ)]

/-- The evenness indicator is nonnegative. -/
theorem ev_nonneg (q : ℕ) : 0 ≤ ev q := by
  unfold ev; split_ifs <;> norm_num

/-- The evenness indicator is at most one. -/
theorem ev_le_one (q : ℕ) : ev q ≤ 1 := by
  unfold ev; split_ifs <;> norm_num

/-- Products of evenness indicators are nonnegative. -/
theorem allEven_nonneg (V : X → Finset E) (L : List (Finset E)) (ξ : X) :
    0 ≤ allEven V L ξ := by
  rw [allEven_eq_fin]
  exact prod_nonneg fun j _ => ev_nonneg _

/-- Products of evenness indicators are at most one. -/
theorem allEven_le_one (V : X → Finset E) (L : List (Finset E)) (ξ : X) :
    allEven V L ξ ≤ 1 := by
  rw [allEven_eq_fin]
  exact prod_le_one (fun j _ => ev_nonneg _) fun j _ => ev_le_one _

/-- The summands defining `Xsum` are nonnegative. -/
theorem term_nonneg (V : X → Finset E) (nb : ℕ) (L : List (Finset E)) (ξ : X) :
    0 ≤ ((#(V ξ)).choose (nb + 1) : ℤ) * allEven V L ξ :=
  mul_nonneg (Int.natCast_nonneg _) (allEven_nonneg V L ξ)

variable [Fintype X]

/-- Vanishing of `Xsum` forces the parity product to vanish above the cutoff. -/
theorem allEven_eq_zero {V : X → Finset E} {nb : ℕ} {L : List (Finset E)}
    (h : Xsum V nb L = 0) {ξ : X} (hξ : nb < #(V ξ)) : allEven V L ξ = 0 := by
  have h1 := (sum_eq_zero_iff_of_nonneg fun ξ _ => term_nonneg V nb L ξ).1 h ξ (mem_univ ξ)
  have h2 : ((#(V ξ)).choose (nb + 1) : ℤ) ≠ 0 :=
    Int.natCast_ne_zero.2 (Nat.choose_pos hξ).ne'
  exact (mul_eq_zero.1 h1).resolve_left h2

/-- Above the cutoff, some check has odd intersection with `V ξ`. -/
theorem good_of_Xsum_eq_zero {V : X → Finset E} {nb : ℕ} {L : List (Finset E)}
    (h : Xsum V nb L = 0) (ξ : X) (hξ : nb < #(V ξ)) :
    ∃ j < L.length, Odd #(L.getD j ∅ ∩ V ξ) := by
  have h1 := allEven_eq_zero h hξ
  rw [allEven_eq_range, prod_eq_zero_iff] at h1
  obtain ⟨j, hj, h2⟩ := h1
  refine ⟨j, mem_range.1 hj, Nat.not_even_iff_odd.1 fun he => ?_⟩
  rw [ev, if_pos he] at h2
  exact one_ne_zero h2

/-- Under vanishing of `Xsum`, the parity product isolates the empty assignment. -/
theorem eta_mul_allEven {V : X → Finset E} {nb : ℕ} {L : List (Finset E)}
    (h : Xsum V nb L = 0) (ξ : X) :
    eta V nb ξ * allEven V L ξ = if V ξ = ∅ then 1 else 0 := by
  rw [allEven_eq_range]
  exact ClauseBound.ParityChecks.StepOne.product V nb L.length
    (fun j => L.getD j ∅) (good_of_Xsum_eq_zero h) ξ

/-- Under vanishing of `Xsum`, `Fsum` counts empty assignments. -/
theorem Fsum_eq {V : X → Finset E} {nb : ℕ} {L : List (Finset E)}
    (h : Xsum V nb L = 0) : Fsum V nb L = #{ξ | V ξ = ∅} := by
  rw [Fsum, card_filter, Nat.cast_sum]
  refine sum_congr rfl fun ξ _ => ?_
  rw [eta_mul_allEven h]
  split_ifs <;> simp

end VariableBound.StepParity

open VariableBound

/-- The residue bounds from Step 1. -/
theorem solution : AppVariables.ResiduesStmt := by
  intro X E _ _ _ V nb L n hX
  have hX' : (Fintype.card X : ℤ) ≤ 2 ^ n := by exact_mod_cast hX
  refine ⟨⟨sum_nonneg fun ξ _ => VariableBound.StepParity.term_nonneg V nb L ξ, ?_, ?_⟩, fun h => ?_⟩
  · have h1 : ∀ ξ ∈ (univ : Finset X),
        ((#(V ξ)).choose (nb + 1) : ℤ) * allEven V L ξ ≤
          ((Fintype.card E).choose (nb + 1) : ℤ) := fun ξ _ =>
      (mul_le_of_le_one_right (Int.natCast_nonneg _)
        (VariableBound.StepParity.allEven_le_one V L ξ)).trans
        (by exact_mod_cast Nat.choose_le_choose (nb + 1) (card_le_univ (V ξ)))
    refine (sum_le_card_nsmul _ _ _ h1).trans ?_
    rw [nsmul_eq_mul, card_univ]
    exact mul_le_mul_of_nonneg_right hX' (Int.natCast_nonneg _)
  · rw [pow_add]
    exact mul_le_mul_of_nonneg_left
      (by exact_mod_cast Nat.le_pow_clog one_lt_two _) (by positivity)
  · rw [VariableBound.StepParity.Fsum_eq h]
    exact ⟨Int.natCast_nonneg _, le_trans (by exact_mod_cast card_le_univ _) hX'⟩

-- Prove2me | solution 1 for VariableBound.product
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:22:13.677978+00:00
-- url     : https://prove2.me/submissions/bc2b99aa-f075-4ec5-8d58-3bd03746edd3

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

end
end

namespace VariableBound.StepParity

open Finset ParityChecks AppVariables

variable {X E : Type} [DecidableEq E]

/-! ### From a list of checks to numbered checks -/

/-- The product over the checks of a list is the product over their numbers j : Fin r; check number
j is `L.getD j ∅`. -/
theorem allEven_eq_fin (V : X → Finset E) (L : List (Finset E)) (ξ : X) : allEven V L ξ = ∏ j : Fin L.length, ev #(L.getD j ∅ ∩ V ξ) := by
  rw [allEven, ← Fin.prod_univ_fun_getElem]
  exact prod_congr rfl fun j _ => by rw [List.getD_eq_getElem _ _ j.isLt]

/-- The product over the checks of a list is the product over their numbers j < r. -/
theorem allEven_eq_range (V : X → Finset E) (L : List (Finset E)) (ξ : X) : allEven V L ξ = ∏ j ∈ range L.length, ev #(L.getD j ∅ ∩ V ξ) := by
  rw [allEven_eq_fin, prod_range fun j => ev #(L.getD j ∅ ∩ V ξ)]

/-- [q even] is at least 0. -/
theorem ev_nonneg (q : ℕ) : 0 ≤ ev q := by
  unfold ev; split_ifs <;> norm_num

/-- [q even] is at most 1. -/
theorem ev_le_one (q : ℕ) : ev q ≤ 1 := by
  unfold ev; split_ifs <;> norm_num

/-- The product over j is at least 0. -/
theorem allEven_nonneg (V : X → Finset E) (L : List (Finset E)) (ξ : X) : 0 ≤ allEven V L ξ := by
  rw [allEven_eq_fin]
  exact prod_nonneg fun j _ => ev_nonneg _

/-- The product over j is at most 1. -/
theorem allEven_le_one (V : X → Finset E) (L : List (Finset E)) (ξ : X) : allEven V L ξ ≤ 1 := by
  rw [allEven_eq_fin]
  exact prod_le_one (fun j _ => ev_nonneg _) fun j _ => ev_le_one _

/-- C(|A|, c)·y as a sum of y over the subsets of A with c elements. -/
theorem choose_mul {E : Type} (A : Finset E) (c : ℕ) (y : ℤ) : ((#A).choose c : ℤ) * y = ∑ _S₀ ∈ A.powerset with #_S₀ = c, y := by
  rw [sum_const, ← powersetCard_eq_filter, card_powersetCard, nsmul_eq_mul]

/-! ### Display (63) -/

/-- The terms of X(𝓛) are nonnegative. -/
theorem term_nonneg (V : X → Finset E) (nb : ℕ) (L : List (Finset E)) (ξ : X) : 0 ≤ ((#(V ξ)).choose (nb + 1) : ℤ) * allEven V L ξ :=
  mul_nonneg (Int.natCast_nonneg _) (allEven_nonneg V L ξ)

variable [Fintype X]

/-- If X(𝓛) = 0, then for every ξ with |V(ξ)| > n̄ the product over j is 0. -/
theorem allEven_eq_zero {V : X → Finset E} {nb : ℕ} {L : List (Finset E)} (h : Xsum V nb L = 0) {ξ : X} (hξ : nb < #(V ξ)) : allEven V L ξ = 0 := by
  have h1 := (sum_eq_zero_iff_of_nonneg fun ξ _ => term_nonneg V nb L ξ).1 h ξ (mem_univ ξ)
  have h2 : ((#(V ξ)).choose (nb + 1) : ℤ) ≠ 0 := Int.natCast_ne_zero.2 (Nat.choose_pos hξ).ne'
  exact (mul_eq_zero.1 h1).resolve_left h2

/-- If X(𝓛) = 0, then every ξ with |V(ξ)| > n̄ violates an odd number of clauses of some check. -/
theorem good_of_Xsum_eq_zero {V : X → Finset E} {nb : ℕ} {L : List (Finset E)} (h : Xsum V nb L = 0) (ξ : X) (hξ : nb < #(V ξ)) :
    ∃ j < L.length, Odd #(L.getD j ∅ ∩ V ξ) := by
  have h1 := allEven_eq_zero h hξ
  rw [allEven_eq_range, prod_eq_zero_iff] at h1
  obtain ⟨j, hj, h2⟩ := h1
  refine ⟨j, mem_range.1 hj, Nat.not_even_iff_odd.1 fun he => ?_⟩
  rw [ev, if_pos he] at h2
  exact one_ne_zero h2

/-- If X(𝓛) = 0, then η(ξ)·∏_j [ |V_j(ξ)| even ] = [V(ξ) = ∅] for every ξ. -/
theorem eta_mul_allEven {V : X → Finset E} {nb : ℕ} {L : List (Finset E)} (h : Xsum V nb L = 0) (ξ : X) :
    eta V nb ξ * allEven V L ξ = if V ξ = ∅ then 1 else 0 := by
  rw [allEven_eq_range]
  exact ClauseBound.ParityChecks.StepOne.product V nb L.length (fun j => L.getD j ∅) (good_of_Xsum_eq_zero h) ξ

/-- If X(𝓛) = 0, then F(𝓛) is the number of ξ with V(ξ) = ∅. -/
theorem Fsum_eq {V : X → Finset E} {nb : ℕ} {L : List (Finset E)} (h : Xsum V nb L = 0) : Fsum V nb L = #{ξ | V ξ = ∅} := by
  rw [Fsum, card_filter, Nat.cast_sum]
  refine sum_congr rfl fun ξ _ => ?_
  rw [eta_mul_allEven h]
  split_ifs <;> simp

end VariableBound.StepParity

theorem solution : AppVariables.ProductStmt := fun _ _ _ _ _ _ _ _ h => VariableBound.StepParity.Fsum_eq h

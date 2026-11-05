-- Prove2me | solution 1 for PaddedDescent.F.Mark.Pi.sum_powerset_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:08:18.320078+00:00
-- url     : https://prove2.me/submissions/432db900-4b8d-4924-87d3-120667e41461

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_PaddedDescent_F_MarkPi

set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Pi
open Finset Groundwork Groundwork.Prog
variable {ι : Type*} [DecidableEq ι]
namespace PaddedDescent.F.Mark.Pi
theorem _root_.solution {A B : Finset ι} (hAB : Disjoint A B) (F G : Finset ι → ℤ) :
    ∑ X ∈ (A ∪ B).powerset, F (X ∩ A) * G (X ∩ B) = (∑ P ∈ A.powerset, F P) * ∑ Q ∈ B.powerset, G Q := by
  rw [sum_mul_sum, ← sum_product']
  symm
  refine sum_nbij' (fun p => p.1 ∪ p.2) (fun X => (X ∩ A, X ∩ B)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨h1, h2⟩ := mem_product.1 hp
    exact mem_powerset.2 (union_subset_union (mem_powerset.1 h1) (mem_powerset.1 h2))
  · intro X _
    exact mem_product.2 ⟨mem_powerset.2 inter_subset_right, mem_powerset.2 inter_subset_right⟩
  · intro p hp
    obtain ⟨h1, h2⟩ := mem_product.1 hp
    have h1 := mem_powerset.1 h1
    have h2 := mem_powerset.1 h2
    have e1 : (p.1 ∪ p.2) ∩ A = p.1 := by
      rw [union_inter_distrib_right, inter_eq_left.2 h1, (disjoint_iff_inter_eq_empty.1 (hAB.symm.mono_left h2)), union_empty]
    have e2 : (p.1 ∪ p.2) ∩ B = p.2 := by
      rw [union_inter_distrib_right, inter_eq_left.2 h2, (disjoint_iff_inter_eq_empty.1 (hAB.mono_left h1)), empty_union]
    exact Prod.ext e1 e2
  · intro X hX
    change X ∩ A ∪ X ∩ B = X
    rw [← inter_union_distrib_left, inter_eq_left.2 (mem_powerset.1 hX)]
  · intro p hp
    obtain ⟨h1, h2⟩ := mem_product.1 hp
    have h1 := mem_powerset.1 h1
    have h2 := mem_powerset.1 h2
    have e1 : (p.1 ∪ p.2) ∩ A = p.1 := by
      rw [union_inter_distrib_right, inter_eq_left.2 h1, (disjoint_iff_inter_eq_empty.1 (hAB.symm.mono_left h2)), union_empty]
    have e2 : (p.1 ∪ p.2) ∩ B = p.2 := by
      rw [union_inter_distrib_right, inter_eq_left.2 h2, (disjoint_iff_inter_eq_empty.1 (hAB.mono_left h1)), empty_union]
    rw [e1, e2]
end PaddedDescent.F.Mark.Pi

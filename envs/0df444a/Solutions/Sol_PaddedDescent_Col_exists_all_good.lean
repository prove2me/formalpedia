-- Prove2me | solution 1 for PaddedDescent.Col.exists_all_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:59:30.590705+00:00
-- url     : https://prove2.me/submissions/390607c6-acdc-4f0b-9b31-06da9f4c2bf7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Push
import Definitions.Def_PaddedDescent_Col_Colouring
import Theorems.Thm_PaddedDescent_Col_card_tail_le
import Theorems.Thm_PaddedDescent_Col_mean_le

set_option autoImplicit false
section
section
open Finset
open PaddedDescent PaddedDescent.Col
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace PaddedDescent.Col
theorem _root_.solution [Nonempty κ] {T : Type*} [Fintype T] (x : T → ι → ℝ) (hx0 : ∀ t b, 0 ≤ x t b) (hx1 : ∀ t b, x t b ≤ 1)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (h : (Fintype.card T : ℝ) * Fintype.card κ * Real.exp (-(δ ^ 2 * ((Fintype.card ι : ℝ) / Fintype.card κ) / 4)) < 1) :
    ∃ χ : ι → κ, ∀ t γ, Wt (x t) γ χ < (∑ b, x t b) / Fintype.card κ + δ * ((Fintype.card ι : ℝ) / Fintype.card κ) := by
  by_contra hne
  push Not at hne
  set s : ℝ := (Fintype.card ι : ℝ) / Fintype.card κ with hs
  set E : ℝ := Real.exp (-(δ ^ 2 * s / 4)) with hE
  set N : ℝ := (Fintype.card κ : ℝ) ^ Fintype.card ι with hN
  have hNpos : 0 < N := by
    have hK : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
    positivity
  let B : T × κ → Finset (ι → κ) := fun p => {χ : ι → κ | (∑ b, x p.1 b) / Fintype.card κ + δ * s ≤ Wt (x p.1) p.2 χ}
  have hcover : (univ : Finset (ι → κ)) ⊆ univ.biUnion B := by
    intro χ _
    obtain ⟨t, γ, hb⟩ := hne χ
    exact Finset.mem_biUnion.2 ⟨(t, γ), Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩⟩
  have h1 : (N : ℝ) ≤ ∑ p : T × κ, (#(B p) : ℝ) := by
    have c1 : #(univ : Finset (ι → κ)) ≤ ∑ p : T × κ, #(B p) := (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    have c2 : (#(univ : Finset (ι → κ)) : ℝ) = N := by
      rw [Finset.card_univ, Fintype.card_fun, hN]; push_cast; rfl
    rw [← c2]
    exact_mod_cast c1
  have h2 : ∑ p : T × κ, (#(B p) : ℝ) ≤ ∑ _p : T × κ, N * E :=
    Finset.sum_le_sum fun p _ => card_tail_le (x p.1) (hx0 p.1) (hx1 p.1) p.2 hδ0 hδ1 (mean_le (x p.1) (hx1 p.1))
  have h3 : ∑ _p : T × κ, N * E = N * ((Fintype.card T : ℝ) * Fintype.card κ * E) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]; push_cast; ring
  have h4 : N * ((Fintype.card T : ℝ) * Fintype.card κ * E) < N * 1 := mul_lt_mul_of_pos_left h hNpos
  linarith
end PaddedDescent.Col

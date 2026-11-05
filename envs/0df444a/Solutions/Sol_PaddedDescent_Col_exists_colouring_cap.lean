-- Prove2me | solution 1 for PaddedDescent.Col.exists_colouring_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:03:13.713072+00:00
-- url     : https://prove2.me/submissions/e8bef425-b14d-4505-8249-a938c7a80eee

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
import Theorems.Thm_PaddedDescent_Col_exists_all_good
import Theorems.Thm_PaddedDescent_Col_Wt_eq

set_option autoImplicit false
section
section
open Finset
open PaddedDescent PaddedDescent.Col
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace PaddedDescent.Col
theorem _root_.solution [Nonempty κ] (c : ι → ι → ℕ) (M D : ℕ) (hM0 : 0 < M) (hD : 1 ≤ D) (hM : ∀ a b, c a b ≤ M)
    (hg : ((Fintype.card ι : ℝ) + 2) * Fintype.card κ *
      Real.exp (-((1 / (D : ℝ)) ^ 2 * ((Fintype.card ι : ℝ) / Fintype.card κ) / 4)) < 1) :
    ∃ χ : ι → κ, (∀ γ, Fintype.card κ * #{a | χ a = γ} < 2 * Fintype.card ι) ∧
      ∀ γ γ', D * Fintype.card κ ^ 2 * ∑ a with χ a = γ, ∑ b with χ b = γ', c a b
        ≤ D * (∑ a, ∑ b, c a b) + 3 * Fintype.card ι ^ 2 * M := by
  have hK1 : (1 : ℝ) ≤ Fintype.card κ := by exact_mod_cast Fintype.card_pos
  have hgpos : 0 < Fintype.card ι := by
    by_contra h0
    have h0' : Fintype.card ι = 0 := by omega
    rw [h0'] at hg
    simp at hg
    linarith
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ, g = Fintype.card ι := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = Fintype.card κ := ⟨_, rfl⟩
  obtain ⟨Mr, hMdef⟩ : ∃ Mr : ℝ, Mr = M := ⟨_, rfl⟩
  obtain ⟨Dr, hDdef⟩ : ∃ Dr : ℝ, Dr = D := ⟨_, rfl⟩
  have hg0 : 0 < g := by rw [hgdef]; exact_mod_cast hgpos
  have hK0 : 0 < K := by rw [hKdef]; linarith
  have hMr : 0 < Mr := by rw [hMdef]; exact_mod_cast hM0
  have hDr : 1 ≤ Dr := by rw [hDdef]; exact_mod_cast hD
  have hδ0 : 0 ≤ 1 / Dr := by positivity
  have hδ1 : 1 / Dr ≤ 1 := by rw [div_le_one (by linarith)]; exact hDr
  let Pr : ι → ℝ := fun a => ∑ b, (c a b : ℝ)
  have hP0 : ∀ a, 0 ≤ Pr a := fun a => Finset.sum_nonneg fun b _ => Nat.cast_nonneg _
  have hcM : ∀ a b, (c a b : ℝ) ≤ Mr := fun a b => by rw [hMdef]; exact_mod_cast hM a b
  have hPle : ∀ a, Pr a ≤ g * Mr := fun a => by
    calc Pr a ≤ ∑ _b : ι, Mr := Finset.sum_le_sum fun b _ => hcM a b
      _ = g * Mr := by simp [hgdef]
  let x : Unit ⊕ ι ⊕ Unit → ι → ℝ := fun t => match t with
    | .inl _ => fun _ => 1
    | .inr (.inl a) => fun b => (c a b : ℝ) / Mr
    | .inr (.inr _) => fun a => Pr a / (g * Mr)
  have hx0 : ∀ t b, 0 ≤ x t b := by
    rintro (_ | a | _) b
    · exact zero_le_one
    · exact div_nonneg (Nat.cast_nonneg _) hMr.le
    · exact div_nonneg (hP0 b) (by positivity)
  have hx1 : ∀ t b, x t b ≤ 1 := by
    rintro (_ | a | _) b
    · exact le_refl _
    · exact (div_le_one hMr).2 (hcM a b)
    · exact (div_le_one (by positivity)).2 (hPle b)
  have hcard : ((Fintype.card (Unit ⊕ ι ⊕ Unit) : ℕ) : ℝ) = g + 2 := by
    simp [Fintype.card_sum, hgdef]; ring
  obtain ⟨χ, hχ⟩ := exists_all_good (κ := κ) x hx0 hx1 hδ0 hδ1 (by rw [hcard, hgdef, hDdef]; exact hg)
  rw [← hgdef, ← hKdef] at hχ
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = g / K := ⟨_, rfl⟩
  rw [← hsdef] at hχ
  have hs0 : 0 < s := by rw [hsdef]; positivity
  -- the three kinds of facts
  have f1 : ∀ γ, ((#{a | χ a = γ} : ℕ) : ℝ) < 2 * s := by
    intro γ
    have h := hχ (.inl ()) γ
    have e1 : Wt (x (.inl ())) γ χ = ((#{a | χ a = γ} : ℕ) : ℝ) := by
      rw [Wt_eq]; simp [x]
    have e2 : (∑ b, x (.inl ()) b) / K = s := by
      rw [hsdef]; simp [x, hgdef]
    rw [e1, e2] at h
    nlinarith
  have f2 : ∀ a γ', ∑ b with χ b = γ', (c a b : ℝ) ≤ Pr a / K + Mr * (1 / Dr * s) := by
    intro a γ'
    have h := hχ (.inr (.inl a)) γ'
    have e1 : Wt (x (.inr (.inl a))) γ' χ = (∑ b with χ b = γ', (c a b : ℝ)) / Mr := by
      rw [Wt_eq, Finset.sum_div]
    have e2 : (∑ b, x (.inr (.inl a)) b) / K = Pr a / K / Mr := by
      have : ∑ b, x (.inr (.inl a)) b = Pr a / Mr := by
        change ∑ b, (c a b : ℝ) / Mr = _
        rw [← Finset.sum_div]
      rw [this]; ring
    rw [e1, e2, div_lt_iff₀ hMr] at h
    have : (Pr a / K / Mr + 1 / Dr * s) * Mr = Pr a / K + Mr * (1 / Dr * s) := by field_simp
    linarith
  have f3 : ∀ γ, ∑ a with χ a = γ, Pr a ≤ (∑ a, Pr a) / K + g * Mr * (1 / Dr * s) := by
    intro γ
    have h := hχ (.inr (.inr ())) γ
    have hgM : 0 < g * Mr := by positivity
    have e1 : Wt (x (.inr (.inr ()))) γ χ = (∑ a with χ a = γ, Pr a) / (g * Mr) := by
      rw [Wt_eq, Finset.sum_div]
    have e2 : (∑ b, x (.inr (.inr ())) b) / K = (∑ a, Pr a) / K / (g * Mr) := by
      have : ∑ b, x (.inr (.inr ())) b = (∑ a, Pr a) / (g * Mr) := by
        change ∑ b, Pr b / (g * Mr) = _
        rw [← Finset.sum_div]
      rw [this]; ring
    rw [e1, e2, div_lt_iff₀ hgM] at h
    have : ((∑ a, Pr a) / K / (g * Mr) + 1 / Dr * s) * (g * Mr) = (∑ a, Pr a) / K + g * Mr * (1 / Dr * s) := by field_simp
    linarith
  refine ⟨χ, fun γ => ?_, fun γ γ' => ?_⟩
  · have h := f1 γ
    rw [hsdef, mul_div_assoc', lt_div_iff₀ hK0, hKdef, hgdef] at h
    have h' : ((Fintype.card κ * #{a | χ a = γ} : ℕ) : ℝ) < ((2 * Fintype.card ι : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h'
  · have y1 : ∑ a with χ a = γ, ∑ b with χ b = γ', (c a b : ℝ)
        ≤ (∑ a with χ a = γ, Pr a) / K + ((#{a | χ a = γ} : ℕ) : ℝ) * (Mr * (1 / Dr * s)) := by
      calc ∑ a with χ a = γ, ∑ b with χ b = γ', (c a b : ℝ)
          ≤ ∑ a with χ a = γ, (Pr a / K + Mr * (1 / Dr * s)) := Finset.sum_le_sum fun a _ => f2 a γ'
        _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_const, nsmul_eq_mul]
    have y2 : (∑ a with χ a = γ, Pr a) / K ≤ ((∑ a, Pr a) / K + g * Mr * (1 / Dr * s)) / K := by
      gcongr; exact f3 γ
    have y3 : ((#{a | χ a = γ} : ℕ) : ℝ) * (Mr * (1 / Dr * s)) ≤ 2 * s * (Mr * (1 / Dr * s)) := by
      gcongr; exact (f1 γ).le
    have y4 : Dr * K ^ 2 * (((∑ a, Pr a) / K + g * Mr * (1 / Dr * s)) / K + 2 * s * (Mr * (1 / Dr * s)))
        = Dr * (∑ a, Pr a) + 3 * g ^ 2 * Mr := by
      rw [hsdef]; field_simp; ring
    have y5 : Dr * K ^ 2 * ∑ a with χ a = γ, ∑ b with χ b = γ', (c a b : ℝ) ≤ Dr * (∑ a, Pr a) + 3 * g ^ 2 * Mr := by
      rw [← y4]
      have : 0 ≤ Dr * K ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith) this
    rw [hDdef, hKdef, hgdef, hMdef] at y5
    have y6 : (∑ a, Pr a) = ((∑ a, ∑ b, c a b : ℕ) : ℝ) := by
      simp only [Pr]; push_cast; rfl
    rw [y6] at y5
    exact_mod_cast y5
end PaddedDescent.Col

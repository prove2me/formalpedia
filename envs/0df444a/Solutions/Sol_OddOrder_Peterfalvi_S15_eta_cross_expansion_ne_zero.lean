-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.eta_cross_expansion_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T15:41:33.578205+00:00
-- url     : https://prove2.me/submissions/16667ee3-2ac5-4e51-a53c-e4ec864f0859

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/Machinery135.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Machinery135

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/Machinery135.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.4), inner-product endgame** (abstract bookkeeping, issue 9013 追記⁶ core (d)):
for an orthonormal grid `η` and vectors `λ°, θ°` orthogonal to each other and to every grid
member, `⟨λ° − δ·∑ᵢ η_{is}, θ° − δ'·∑ⱼ η_{rj}⟩ = δ·δ' ≠ 0` for signs `δ, δ' = ±1` — the only
surviving term of the bilinear expansion is the shared grid entry `⟨η_{rs}, η_{rs}⟩ = 1`.

In (13.4) the left side is `(α^τ, β^τ)` for `α = λ − μ_s ∈ ℤ[𝒮, H^#]`, `β = θ − ν_r ∈ ℤ[𝒯, K^#]`,
which *vanishes* because `(H^#)^G` and `(K^#)^G` are disjoint TI-supports — the contradiction
closing (13.4). -/
theorem _root_.solution [Fintype G] [Invertible (Nat.card G : ℂ)] {q p : ℕ}
    (eta : Fin q → Fin p → ClassFunction G ℂ)
    (horth : ∀ (i k : Fin q) (j l : Fin p),
      ClassFunction.inner (eta i j) (eta k l) = if i = k ∧ j = l then 1 else 0)
    (lam theta : ClassFunction G ℂ) (r : Fin q) (s : Fin p)
    (hlam_eta : ∀ (i : Fin q) (j : Fin p), ClassFunction.inner lam (eta i j) = 0)
    (heta_theta : ∀ (i : Fin q) (j : Fin p), ClassFunction.inner (eta i j) theta = 0)
    (hlam_theta : ClassFunction.inner lam theta = 0)
    {δ δ' : ℤ} (hδ : δ = 1 ∨ δ = -1) (hδ' : δ' = 1 ∨ δ' = -1) :
    ClassFunction.inner (lam - (δ : ℂ) • ∑ i : Fin q, eta i s)
      (theta - (δ' : ℂ) • ∑ j : Fin p, eta r j) ≠ 0 := by
  have hgrid : ClassFunction.inner (∑ i : Fin q, eta i s) (∑ j : Fin p, eta r j) = 1 := by
    rw [OddOrder.RepresentationTheory.inner_sum_left]
    have hrow : ∀ i : Fin q,
        ClassFunction.inner (eta i s) (∑ j : Fin p, eta r j)
          = if i = r then (1 : ℂ) else 0 := by
      intro i
      rw [OddOrder.RepresentationTheory.inner_sum_right]
      by_cases hir : i = r
      · subst hir
        simp only [horth]
        simp
      · simp only [horth]
        simp [hir]
    rw [Finset.sum_congr rfl fun i _ => hrow i]
    simp
  have hexp : ClassFunction.inner (lam - (δ : ℂ) • ∑ i : Fin q, eta i s)
      (theta - (δ' : ℂ) • ∑ j : Fin p, eta r j) = (δ : ℂ) * (δ' : ℂ) := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, ClassFunction.inner_smul_left,
      ClassFunction.inner_smul_right, ClassFunction.inner_smul_left,
      ClassFunction.inner_smul_right, star_intCast, hlam_theta, hgrid]
    have hlam_sum : ClassFunction.inner lam (∑ j : Fin p, eta r j) = 0 := by
      rw [OddOrder.RepresentationTheory.inner_sum_right]
      exact Finset.sum_eq_zero fun j _ => hlam_eta r j
    have hsum_theta : ClassFunction.inner (∑ i : Fin q, eta i s) theta = 0 := by
      rw [OddOrder.RepresentationTheory.inner_sum_left]
      exact Finset.sum_eq_zero fun i _ => heta_theta i s
    rw [hlam_sum, hsum_theta]
    ring
  rw [hexp]
  rcases hδ with rfl | rfl <;> rcases hδ' with rfl | rfl <;> norm_num

end OddOrder.Peterfalvi.S15

-- Prove2me | solution 1 for OddOrder.Peterfalvi.S09.Hypothesis78.chiRho_norm_sq_eq_card_ratio_mul
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T07:46:09.865135+00:00
-- url     : https://prove2.me/submissions/3ceacfee-e7e7-419f-a6c4-47e679c3affb

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/CoherenceFormula.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_QuadraticTerm
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_CoherenceFormula

-- ===== OddOrder/Peterfalvi/S09_NonexistenceCertain/CoherenceFormula.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open OddOrder.GroupTheory (IsTISubset)

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

section Section_7_8

namespace Hypothesis78

variable {G : Type*} [Group G] [Fintype G]

variable {A : Set G} {L : Subgroup G} [Fintype L]

variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- **Peterfalvi (7.8.c.i).**  For χ ∈ Irr G orthogonal to `S^ν` and `x ∈ A`,
`χ^ρ(x) = star (β, χ)_G`. -/
theorem chiRho_eq_inner_beta_on_A (H78 : Hypothesis78 G A L)
    (χ : ClassFunction G ℂ) (hχ_irr : IsIrreducibleCharacter χ)
    (hχ_orth : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
      ClassFunction.inner χ (H78.nu (H78.hyp76.zeta i)) = 0)
    {x : L} (hx : (x : G) ∈ A) :
    H78.hyp76.hyp71.chiRho χ x = star (ClassFunction.inner H78.beta χ) := by
  rw [beta_def]
  exact H78.chiRho_eq_inner_beta χ hχ_irr hχ_orth hx

/-- **Peterfalvi (7.8.c.ii).**  For χ ∈ Irr G orthogonal to `S^ν`,
`‖χ^ρ‖² = (|A|/|L|) · (β, χ)_G · star (β, χ)_G`.

Proof: the inner-product `(χ^ρ, χ^ρ)_L = (1/|L|) Σ_{l : L} χ^ρ(l) · star (χ^ρ(l))`.
By (7.8.c.i), on `{l ∈ L | (l:G) ∈ A}` each summand equals
`star (β,χ) · (β,χ)`; off it the summand vanishes since `chiRho` is supported
on `A`.  The count of `l : L` with `(l : G) ∈ A` equals `|A|` since `A ⊆ L`
(by `Hypothesis71.card_supportInSubgroup_eq_card_A`). -/
theorem _root_.solution (H78 : Hypothesis78 G A L)
    (χ : ClassFunction G ℂ) (hχ_irr : IsIrreducibleCharacter χ)
    (hχ_orth : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
      ClassFunction.inner χ (H78.nu (H78.hyp76.zeta i)) = 0) :
    ClassFunction.inner (H78.hyp76.hyp71.chiRhoCF χ) (H78.hyp76.hyp71.chiRhoCF χ) =
      ((Nat.card A : ℂ) / (Nat.card L : ℂ)) *
        (ClassFunction.inner H78.beta χ *
          star (ClassFunction.inner H78.beta χ)) := by
  classical
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum, invOf_eq_inv,
      ClassFunction.innerSum]
  -- Pointwise: each summand is a constant on `{l | (l:G) ∈ A}` and zero off it.
  have hpt : ∀ l : L,
      H78.hyp76.hyp71.chiRhoCF χ l * star (H78.hyp76.hyp71.chiRhoCF χ l) =
        if (l : G) ∈ A then
          star (ClassFunction.inner H78.beta χ) *
            ClassFunction.inner H78.beta χ
        else 0 := by
    intro l
    rw [Hypothesis71.chiRhoCF_apply]
    by_cases hl : (l : G) ∈ A
    · rw [if_pos hl,
          H78.chiRho_eq_inner_beta_on_A χ hχ_irr hχ_orth hl, star_star]
    · rw [if_neg hl, H78.hyp76.hyp71.chiRho_of_not_mem χ hl, star_zero,
          mul_zero]
  -- Aggregate the pointwise rewrite, then convert the indicator sum to a count.
  rw [show ∑ l : L,
        H78.hyp76.hyp71.chiRhoCF χ l * star (H78.hyp76.hyp71.chiRhoCF χ l) =
      ∑ l : L,
        if (l : G) ∈ A then
          star (ClassFunction.inner H78.beta χ) *
            ClassFunction.inner H78.beta χ
        else 0 from
    Finset.sum_congr rfl (fun l _ => hpt l)]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  -- The filter count equals `Nat.card A` via `card_supportInSubgroup_eq_card_A`.
  have hcard :
      ((Finset.univ.filter (fun l : L => (l : G) ∈ A)).card : ℂ) =
        (Nat.card A : ℂ) := by
    have hset_eq :
        Finset.univ.filter (fun l : L => (l : G) ∈ A) =
          (OddOrder.Peterfalvi.S04.supportInSubgroup A L).toFinset := by
      ext l
      simp
    rw [hset_eq, Set.toFinset_card, ← Nat.card_eq_fintype_card,
        Hypothesis71.card_supportInSubgroup_eq_card_A
          H78.hyp76.hyp71.hyp.subset_L]
  rw [hcard]
  ring

end Hypothesis78

end Section_7_8

end OddOrder.Peterfalvi.S09

-- Prove2me | solution 1 for Wolf.fg_lcsFactor_and_growth_bounds_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-23T09:38:06.579203+00:00
-- url     : https://prove2.me/submissions/c9589d60-c9d4-463b-bb1f-0d83f83e7494

import Definitions.Def_Chou_Growth
import Mathlib
import Definitions.Def_MilnorWolf_Growth
import Theorems.Thm_Wolf_exists_commutator_generating_sets_with_free_finiteIndex_subfamily_lowerCentralSeries
import Theorems.Thm_Wolf_exists_const_mul_pow_growthExponentOne_le_growthFunction_of_isNilpotent
import Theorems.Thm_Wolf_exists_growthFunction_le_const_mul_pow_growthExponentTwo_of_isNilpotent

/-!
# Chou §3, p. 399: the growth rate of a finitely generated group

Milnor's observation that `|B(n)|^{1/n}` converges, and Wolf's observation that exponential
growth does not depend on the choice of finite generating set.  Both come from Fekete's lemma
applied to the subadditive sequence `n ↦ log |B(n)|`: Mathlib's `Subadditive.lim` is *defined*
as the infimum of `u n / n` over `n ≥ 1`, so the limit `v` satisfies `v ^ n ≤ |B(n)|` for
**every** `n`, not merely eventually — which is what the `∀ n` in `HasExponentialGrowth` needs.
-/

namespace Chou
namespace Lib

open Chou

variable {G : Type*} [Group G]

/-! ### Elementary properties of word balls -/

/-! ### Finiteness and cardinality of balls -/

/-! ### Fekete's lemma applied to `log |B(n)|` -/

/-! ### The two theorems -/

end Lib
end Chou

/-!
# Finite generation: the two directions across a finite-index subgroup

Mathlib has Schreier's lemma `Subgroup.fg_of_index_ne_zero`, that a finite-index subgroup of a
finitely generated group is finitely generated.  Wolf's Proposition 4.1 needs the converse as
well, that finite generation passes *up* from a finite-index subgroup, and the standard
"generators of the quotient together with the kernel" principle.
-/

namespace Wolf
namespace Lib

open Subgroup

/-- Transport finite generation along an isomorphism. -/
theorem fg_of_mulEquiv {A B : Type*} [Group A] [Group B] [Group.FG A] (e : A ≃* B) :
    Group.FG B :=
  Group.fg_of_surjective (f := (e : A →* B)) e.surjective

end Lib
end Wolf

/-!
# The lower central series: plumbing

The terms `Γ_k` of the lower central series, the canonical surjection `Γ_k → Γ_k/Γ_{k+1}` of the
definition bundle, and the consequence that a finitely generated factor is witnessed by finitely
many elements of `Γ_k` together with `Γ_{k+1}`.

These were part of the nilpotent-groups module, which imports Wolf's Theorem 3.2; they are
separated out because a solution *of* Theorem 3.2 needs them and cannot import it.
-/

namespace Wolf
namespace Lib

open Subgroup

variable {Γ : Type*} [Group Γ]

/-- The canonical surjection `Γ_k → Γ_k/Γ_{k+1}` of the definition bundle, which factors
through the abelianization of `Γ_k` because `⁅Γ_k, Γ_k⁆ ≤ Γ_{k+1}`. -/
noncomputable def toLcsFactor (k : ℕ) :
    ↥(MilnorWolf.lcs Γ k) →* MilnorWolf.lcsFactor Γ k :=
  (QuotientGroup.mk' _).comp Abelianization.of

theorem toLcsFactor_surjective (k : ℕ) : Function.Surjective (toLcsFactor (Γ := Γ) k) :=
  (QuotientGroup.mk'_surjective _).comp (fun x => Quot.inductionOn x fun y => ⟨y, rfl⟩)

end Lib
end Wolf

/-!
# The lower-central factor in the shape Lemma 3.7 states it

Lemma 3.7 describes `Γ_k/Γ_{k+1}` as the quotient of the subgroup `Γ_k` by `Γ_{k+1}` sitting
inside it, while the published growth bundle's `lcsFactor` goes through the abelianization of
`Γ_k`.  This module holds the comparison, and the first half of Theorem 3.2 that follows from
it: every lower-central factor of a finitely generated nilpotent group is finitely generated.

Separated from the Theorem 3.2 module because that one imports the two published statements of
the growth bounds, so nothing in it could be used by a proof *of* either bound.
-/

namespace Wolf
namespace Lib

open Chou Chou.Lib

variable {Γ : Type*} [Group Γ]

/-- `Γ_k/Γ_{k+1}` in the shape Lemma 3.7 states it. -/
abbrev lcsQuot (Γ : Type*) [Group Γ] (k : ℕ) : Type _ :=
  ↥(MilnorWolf.lcs Γ k) ⧸ ((MilnorWolf.lcs Γ (k + 1)).subgroupOf (MilnorWolf.lcs Γ k))

/-- `Γ_{k+1}`, viewed inside `Γ_k`, is killed by the projection onto the definition bundle's
factor `lcsFactor Γ k`. -/
theorem subgroupOf_le_ker_toLcsFactor (k : ℕ) :
    (MilnorWolf.lcs Γ (k + 1)).subgroupOf (MilnorWolf.lcs Γ k) ≤
      (toLcsFactor (Γ := Γ) k).ker := by
  intro x hx
  rw [MonoidHom.mem_ker, toLcsFactor, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  exact ⟨x, hx, rfl⟩

/-- The projection of `Γ_k/Γ_{k+1}` onto the definition bundle's `lcsFactor Γ k`. -/
noncomputable def lcsQuotToFactor (k : ℕ) : lcsQuot Γ k →* MilnorWolf.lcsFactor Γ k :=
  QuotientGroup.lift _ (toLcsFactor (Γ := Γ) k) (subgroupOf_le_ker_toLcsFactor k)

theorem lcsQuotToFactor_surjective (k : ℕ) :
    Function.Surjective (lcsQuotToFactor (Γ := Γ) k) := by
  intro y
  obtain ⟨x, rfl⟩ := toLcsFactor_surjective (Γ := Γ) k y
  exact ⟨QuotientGroup.mk' _ x, rfl⟩

/-- The definition bundle's `lcsFactor Γ k` is a quotient of `Γ_k/Γ_{k+1}`. -/
theorem fg_lcsFactor_of_fg_lcsQuot (k : ℕ) (h : Group.FG (lcsQuot Γ k)) :
    Group.FG (MilnorWolf.lcsFactor Γ k) :=
  Group.fg_of_surjective (f := lcsQuotToFactor (Γ := Γ) k) (lcsQuotToFactor_surjective k)

/-- The hypotheses Lemma 3.7 asks for, for a finitely generated nilpotent group. -/
theorem lcs_nilpotencyClass_eq_bot [Group.IsNilpotent Γ] :
    MilnorWolf.lcs Γ (Group.nilpotencyClass Γ) = ⊥ :=
  Subgroup.lowerCentralSeries_nilpotencyClass

theorem fg_lcsQuot_zero [Group.FG Γ] : Group.FG (lcsQuot Γ 0) := by
  haveI : Group.FG ↥(MilnorWolf.lcs Γ 0) :=
    fg_of_mulEquiv (Subgroup.topEquiv (G := Γ)).symm
  exact Group.fg_of_surjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)

/-- **Theorem 3.2, first half**: every lower-central factor of a finitely generated nilpotent
group is finitely generated.  This is Lemma 3.7 (i). -/
theorem forall_fg_lcsFactor [Group.FG Γ] [Group.IsNilpotent Γ] (k : ℕ) :
    Group.FG (MilnorWolf.lcsFactor Γ k) := by
  obtain ⟨r, τ, hi, -, -⟩ :=
    _root_.Wolf.exists_commutator_generating_sets_with_free_finiteIndex_subfamily_lowerCentralSeries
      (Γ := Γ) (Group.nilpotencyClass Γ)
      (by
        have h := lcs_nilpotencyClass_eq_bot (Γ := Γ)
        have hle : MilnorWolf.lcs Γ (Group.nilpotencyClass Γ + 1) ≤
            MilnorWolf.lcs Γ (Group.nilpotencyClass Γ) :=
          (⊤ : Subgroup Γ).lowerCentralSeries_antitone (Nat.le_succ _)
        rw [h] at hle
        exact le_bot_iff.1 hle)
      fg_lcsQuot_zero
  exact fg_lcsFactor_of_fg_lcsQuot k (hi k).1

end Lib
end Wolf

/-!
# Wolf's Theorem 3.2 (p. 425), first half

“Let `Γ` be a finitely generated nilpotent group with lower central series
`Γ = Γ₀ ⊇ Γ₁ ⊇ ⋯ ⊇ Γ_s ⊇ Γ_{s+1} = 1`.  Then each `Γ_k/Γ_{k+1}` is a finitely generated abelian
group, and for any finite generating set `S` there are constants `0 < c₁ ≤ c₂` with
`c₁ m^{E₁} ≤ g_S(m) ≤ c₂ m^{E₂}` for every `m ≥ 1`.”

The finite generation of the factors is the content of Lemma 3.7 (i), so it is read off from
that lemma here; what the lemma needs as input is that `Γ/Γ₁` is finitely generated, which is
immediate for a finitely generated `Γ`, and a step `s` at which the series reaches the trivial
subgroup, which is the nilpotency class.
-/

namespace Wolf
namespace Lib

open Chou Chou.Lib

variable {Γ : Type*} [Group Γ]

/-- **Wolf's Theorem 3.2** (p. 425).  Finite generation of the lower-central factors comes from
Lemma 3.7; the two bounds are the two published halves.  The statement asks for a single pair
`0 < c₁ ≤ c₂`, so the constants are combined by taking their minimum and maximum. -/
theorem fg_lcsFactor_and_growth_bounds_of_isNilpotent' [Group.FG Γ] [Group.IsNilpotent Γ]
    (S : Finset Γ) (hS : Subgroup.closure (S : Set Γ) = ⊤) :
    (∀ k : ℕ, Group.FG (MilnorWolf.lcsFactor Γ k)) ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ ∀ m : ℕ, 1 ≤ m →
        c₁ * (m : ℝ) ^ (MilnorWolf.growthExponentOne Γ) ≤ (MilnorWolf.growthFunction S m : ℝ) ∧
          (MilnorWolf.growthFunction S m : ℝ) ≤
            c₂ * (m : ℝ) ^ (MilnorWolf.growthExponentTwo Γ) := by
  refine ⟨fun k => forall_fg_lcsFactor k, ?_⟩
  obtain ⟨c₁, hc₁, hlow⟩ :=
    _root_.Wolf.exists_const_mul_pow_growthExponentOne_le_growthFunction_of_isNilpotent S hS
  obtain ⟨c₂, hc₂, hup⟩ :=
    _root_.Wolf.exists_growthFunction_le_const_mul_pow_growthExponentTwo_of_isNilpotent S hS
  refine ⟨min c₁ c₂, max c₁ c₂, lt_min hc₁ hc₂, min_le_max, fun m hm => ⟨?_, ?_⟩⟩
  · refine le_trans ?_ (hlow m hm)
    have hpow : (0 : ℝ) ≤ (m : ℝ) ^ (MilnorWolf.growthExponentOne Γ) := by positivity
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) hpow
  · refine le_trans (hup m hm) ?_
    have hpow : (0 : ℝ) ≤ (m : ℝ) ^ (MilnorWolf.growthExponentTwo Γ) := by positivity
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hpow

end Lib
end Wolf

open Wolf

theorem solution {Γ : Type*} [Group Γ] [Group.FG Γ]
    [Group.IsNilpotent Γ] (S : Finset Γ) (hS : Subgroup.closure (S : Set Γ) = ⊤) :
    (∀ k : ℕ, Group.FG (MilnorWolf.lcsFactor Γ k)) ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ ∀ m : ℕ, 1 ≤ m →
        c₁ * (m : ℝ) ^ (MilnorWolf.growthExponentOne Γ) ≤ (MilnorWolf.growthFunction S m : ℝ) ∧
          (MilnorWolf.growthFunction S m : ℝ) ≤
            c₂ * (m : ℝ) ^ (MilnorWolf.growthExponentTwo Γ) :=
  Wolf.Lib.fg_lcsFactor_and_growth_bounds_of_isNilpotent' S hS

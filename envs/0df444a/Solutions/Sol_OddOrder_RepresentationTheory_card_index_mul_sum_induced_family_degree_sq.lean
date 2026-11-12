-- Prove2me | solution 1 for OddOrder.RepresentationTheory.card_index_mul_sum_induced_family_degree_sq
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:39:03.941968+00:00
-- url     : https://prove2.me/submissions/15b7616f-2f3c-4804-a3e8-35dccf4b20d0

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/ColumnOrthogonality.lean
--   OddOrder/GroupTheory/RepresentationTheory/InducedDegreeSum.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterCompleteness
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterRowOrthogonality
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ZIrrFourier
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality

-- ===== OddOrder/GroupTheory/RepresentationTheory/ColumnOrthogonality.lean =====
namespace OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Finite G]

open scoped Classical in
/-- **Burnside degree-sum identity, nontrivial part** (Peterfalvi (1.5.d)).

Summing the squared degrees over the *nontrivial* irreducible characters (i.e. all `χ`
except the trivial character, whose degree is `1`) gives `|G| - 1`:
`∑_{χ ∈ Irr G, χ ≠ 1} χ(1)² = |G| - 1` in `ℂ`. -/
theorem sumNontrivialIrreducibleDegreeSq :
    ∑ χ ∈ Finset.univ.erase (trivialIrreducibleCharacter G),
        ((χ : ClassFunction G ℂ) 1) ^ 2 = (Nat.card G : ℂ) - 1 := by
  have htriv : ((trivialIrreducibleCharacter G : ClassFunction G ℂ) 1) ^ 2 = 1 := by
    simp
  have hsplit :=
    Finset.add_sum_erase (Finset.univ : Finset (IrreducibleCharacter G))
      (fun χ => ((χ : ClassFunction G ℂ) 1) ^ 2)
      (a := trivialIrreducibleCharacter G) (Finset.mem_univ _)
  rw [htriv] at hsplit
  rw [eq_sub_iff_add_eq, add_comm, hsplit, sumIrreducibleDegreeSq]

end OddOrder.RepresentationTheory

-- ===== OddOrder/GroupTheory/RepresentationTheory/InducedDegreeSum.lean =====
set_option linter.unusedFintypeInType false

namespace OddOrder.RepresentationTheory

open ClassFunction

variable {G : Type*} [Group G] {H : Subgroup G} [hH : H.Normal]

variable [Fintype G] [Fintype ↥H]

variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥H : ℂ)]

omit [Fintype G] [Fintype ↥H] [Invertible (Nat.card G : ℂ)]
  [Invertible (Nat.card ↥H : ℂ)] in
/-- Conjugating the trivial irreducible character gives back the trivial character. -/
theorem IrreducibleCharacter.conjBy_trivial (g : G) :
    IrreducibleCharacter.conjBy g (trivialIrreducibleCharacter ↥H)
      = trivialIrreducibleCharacter ↥H := by
  apply IrreducibleCharacter.ext
  rw [IrreducibleCharacter.coe_conjBy]
  ext x
  rw [ClassFunction.conjBy_apply]
  rfl

/-- **The trivial induced character is orthogonal to a nontrivial induced irreducible.**
`⟨Ind_H^G φ, Ind_H^G 1_H⟩ = 0` for `φ ≠ 1_H`: every Mackey summand `⟨φ, 1_H^{x⁻¹}⟩ = ⟨φ, 1_H⟩`
vanishes by orthonormality. -/
theorem inner_induce_induce_trivial_eq_zero
    {φ : IrreducibleCharacter ↥H} (hφ : φ ≠ trivialIrreducibleCharacter ↥H) :
    ClassFunction.inner (induce H (φ : ClassFunction ↥H ℂ))
      (induce H (trivialIrreducibleCharacter ↥H : ClassFunction ↥H ℂ)) = 0 := by
  have hcardH : (Nat.card ↥H : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact Nat.card_pos.ne'
  apply mul_left_cancel₀ hcardH
  rw [mul_zero, card_mul_inner_induce]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [← IrreducibleCharacter.coe_conjBy, IrreducibleCharacter.conjBy_trivial,
    irreducibleCharacter_inner_eq_ite, if_neg hφ]

/-- **The trivial induced character is orthogonal to a nontrivial induced irreducible**, swapped
form.  `⟨Ind_H^G 1_H, Ind_H^G φ⟩ = 0` for `φ ≠ 1_H`: every Mackey summand `⟨1_H, φ^{x⁻¹}⟩`
vanishes since `φ^{x⁻¹} ≠ 1_H` (conjugation preserves nontriviality). -/
theorem inner_induce_trivial_induce_eq_zero
    {φ : IrreducibleCharacter ↥H} (hφ : φ ≠ trivialIrreducibleCharacter ↥H) :
    ClassFunction.inner (induce H (trivialIrreducibleCharacter ↥H : ClassFunction ↥H ℂ))
      (induce H (φ : ClassFunction ↥H ℂ)) = 0 := by
  have hcardH : (Nat.card ↥H : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact Nat.card_pos.ne'
  apply mul_left_cancel₀ hcardH
  rw [mul_zero, card_mul_inner_induce]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [← IrreducibleCharacter.coe_conjBy, irreducibleCharacter_inner_eq_ite, if_neg]
  intro h
  refine hφ ?_
  have := congrArg (IrreducibleCharacter.conjBy (G := G) x) h.symm
  rwa [IrreducibleCharacter.conjBy_conjBy_inv,
    IrreducibleCharacter.conjBy_trivial (H := H) x] at this

/-- **The `Irr H`-summed cross inner product against a fixed induced character is `[G:H]`.**
`∑_{φ ∈ Irr H} ⟨Ind_H^G φ, Ind_H^G ψ⟩ = [G : H]` for any `ψ ∈ Irr H`: by the Mackey formula
each `x ∈ G` contributes `∑_φ ⟨φ, ψ^{x⁻¹}⟩ = 1` (exactly one irreducible equals `ψ^{x⁻¹}`), so
the double sum is `|G|`, and dividing by `|H|` gives the index. -/
theorem sum_inner_induce_induce_eq_index (ψ : IrreducibleCharacter ↥H) :
    ∑ φ : IrreducibleCharacter ↥H,
        ClassFunction.inner (induce H (φ : ClassFunction ↥H ℂ))
          (induce H (ψ : ClassFunction ↥H ℂ))
      = (H.index : ℂ) := by
  classical
  have hcardH : (Nat.card ↥H : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact Nat.card_pos.ne'
  apply mul_left_cancel₀ hcardH
  rw [Finset.mul_sum]
  have hterm : ∀ φ : IrreducibleCharacter ↥H,
      (Nat.card ↥H : ℂ) * ClassFunction.inner (induce H (φ : ClassFunction ↥H ℂ))
          (induce H (ψ : ClassFunction ↥H ℂ))
        = ∑ x : G, ClassFunction.inner (φ : ClassFunction ↥H ℂ)
            ((IrreducibleCharacter.conjBy x⁻¹ ψ : IrreducibleCharacter ↥H) :
              ClassFunction ↥H ℂ) := by
    intro φ
    rw [card_mul_inner_induce]
    exact Finset.sum_congr rfl fun x _ => by rw [IrreducibleCharacter.coe_conjBy]
  rw [Finset.sum_congr rfl fun φ _ => hterm φ, Finset.sum_comm]
  have hinner : ∀ x : G,
      ∑ φ : IrreducibleCharacter ↥H,
          ClassFunction.inner (φ : ClassFunction ↥H ℂ)
            ((IrreducibleCharacter.conjBy x⁻¹ ψ : IrreducibleCharacter ↥H) :
              ClassFunction ↥H ℂ)
        = 1 := by
    intro x
    rw [Finset.sum_congr rfl fun φ _ => irreducibleCharacter_inner_eq_ite φ _]
    rw [Finset.sum_ite_eq' Finset.univ (IrreducibleCharacter.conjBy x⁻¹ ψ) (fun _ => (1 : ℂ))]
    rw [if_pos (Finset.mem_univ _)]
  rw [Finset.sum_congr rfl fun x _ => hinner x, Finset.sum_const, Finset.card_univ]
  rw [nsmul_eq_mul, mul_one, ← Nat.card_eq_fintype_card, ← H.index_mul_card, Nat.cast_mul]
  ring

section Frobenius

variable {C : Subgroup G}

open scoped Classical in
/-- **Fiber size of the induction map on `Irr H` is the index** (Frobenius case).  For a
Frobenius group `(G, H, C)` and a nontrivial `ψ ∈ Irr H`, the number of irreducible characters
of `H` inducing to `Ind_H^G ψ` is exactly `[G : H]`.  The `Irr H`-summed cross inner product is
`[G:H]` (`sum_inner_induce_induce_eq_index`), while each summand is `1` for fiber members
(`inner_self_induce_eq_one_of_frobeniusGroup`) and `0` otherwise (distinct irreducibles for
nontrivial `φ`, and `inner_induce_induce_trivial_eq_zero` for `φ = 1_H`). -/
theorem card_induce_fiber_of_frobeniusGroup
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G H C)
    (ψ : IrreducibleCharacter ↥H) (hψ : ψ ≠ trivialIrreducibleCharacter ↥H) :
    (Finset.univ.filter (fun φ : IrreducibleCharacter ↥H =>
        induce H (φ : ClassFunction ↥H ℂ) = induce H (ψ : ClassFunction ↥H ℂ))).card
      = H.index := by
  classical
  have hsum := sum_inner_induce_induce_eq_index (H := H) ψ
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun φ : IrreducibleCharacter ↥H =>
      induce H (φ : ClassFunction ↥H ℂ) = induce H (ψ : ClassFunction ↥H ℂ))] at hsum
  -- Fiber members contribute `1` each.
  have hfiber : ∀ φ ∈ Finset.univ.filter (fun φ : IrreducibleCharacter ↥H =>
      induce H (φ : ClassFunction ↥H ℂ) = induce H (ψ : ClassFunction ↥H ℂ)),
      ClassFunction.inner (induce H (φ : ClassFunction ↥H ℂ))
        (induce H (ψ : ClassFunction ↥H ℂ)) = 1 := by
    intro φ hφ
    rw [Finset.mem_filter] at hφ
    rw [hφ.2]
    exact inner_self_induce_eq_one_of_frobeniusGroup hF ψ hψ
  -- Non-members contribute `0` each.
  have hoff : ∀ φ ∈ Finset.univ.filter (fun φ : IrreducibleCharacter ↥H =>
      ¬ induce H (φ : ClassFunction ↥H ℂ) = induce H (ψ : ClassFunction ↥H ℂ)),
      ClassFunction.inner (induce H (φ : ClassFunction ↥H ℂ))
        (induce H (ψ : ClassFunction ↥H ℂ)) = 0 := by
    intro φ hφ
    rw [Finset.mem_filter] at hφ
    by_cases hφtriv : φ = trivialIrreducibleCharacter ↥H
    · subst hφtriv
      exact inner_induce_trivial_induce_eq_zero (H := H) hψ
    · -- Both induced characters are irreducible and distinct.
      have hφirr : IsIrreducibleCharacter (induce H (φ : ClassFunction ↥H ℂ)) :=
        isIrreducibleCharacter_induce_of_frobeniusGroup hF φ hφtriv
      have hψirr : IsIrreducibleCharacter (induce H (ψ : ClassFunction ↥H ℂ)) :=
        isIrreducibleCharacter_induce_of_frobeniusGroup hF ψ hψ
      have h := irreducibleCharacter_inner_eq_ite
        (⟨_, hφirr⟩ : IrreducibleCharacter G) ⟨_, hψirr⟩
      rwa [if_neg (fun heq => hφ.2 (congrArg Subtype.val heq))] at h
  rw [Finset.sum_congr rfl hfiber, Finset.sum_congr rfl hoff, Finset.sum_const,
    Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_zero, add_zero] at hsum
  exact_mod_cast hsum

/-- **Degree-square sum of a Frobenius induced family** (Peterfalvi's `∑ a_i² = (h−1)/e`,
multiplied out).  Given an enumeration `θ : Fin (n+1) → Irr H` of the distinct induced
characters (injective + covering) with the trivial character at `ind1H`, the Frobenius
structure forces every fiber of `θ ↦ Ind θ` over `Irr H ∖ {1}` to have size `e = [G:H]`
(`card_induce_fiber_of_frobeniusGroup`) with constant degree, so the Burnside sum
`∑_{φ ≠ 1} φ(1)² = |H| − 1` (`sumNontrivialIrreducibleDegreeSq`) collapses to
`e · ∑_{i ≠ ind1H} θ_i(1)²`. -/
theorem _root_.solution
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G H C)
    {n : ℕ} (θ : Fin (n + 1) → IrreducibleCharacter ↥H) (ind1H : Fin (n + 1))
    (htriv : θ ind1H = trivialIrreducibleCharacter ↥H)
    (hinj : Function.Injective
      (fun i => induce H (θ i : ClassFunction ↥H ℂ)))
    (hcover : ∀ φ : IrreducibleCharacter ↥H,
      induce H (φ : ClassFunction ↥H ℂ) ∈
        Set.range (fun i => induce H (θ i : ClassFunction ↥H ℂ))) :
    (H.index : ℂ) * ∑ i ∈ Finset.univ.erase ind1H,
        ((θ i : ClassFunction ↥H ℂ) 1) ^ 2
      = (Nat.card ↥H : ℂ) - 1 := by
  classical
  -- The classifier `c φ = i` iff `Ind φ = Ind θ_i` (unique by `hinj`).
  have hc : ∀ φ : IrreducibleCharacter ↥H, ∃ i : Fin (n + 1),
      induce H (φ : ClassFunction ↥H ℂ) = induce H (θ i : ClassFunction ↥H ℂ) := by
    intro φ
    obtain ⟨i, hi⟩ := hcover φ
    exact ⟨i, hi.symm⟩
  set c : IrreducibleCharacter ↥H → Fin (n + 1) := fun φ => (hc φ).choose with hc_def
  have hc_spec : ∀ φ : IrreducibleCharacter ↥H,
      induce H (φ : ClassFunction ↥H ℂ) = induce H (θ (c φ) : ClassFunction ↥H ℂ) :=
    fun φ => (hc φ).choose_spec
  -- Nontrivial `φ` never classifies to `ind1H`.
  have hθ_ne : ∀ i : Fin (n + 1), i ≠ ind1H → θ i ≠ trivialIrreducibleCharacter ↥H := by
    intro i hi h
    exact hi (hinj (by simp only [h, htriv]))
  have hc_ne : ∀ φ : IrreducibleCharacter ↥H, φ ≠ trivialIrreducibleCharacter ↥H →
      c φ ≠ ind1H := by
    intro φ hφ hcφ
    have h1 : induce H (φ : ClassFunction ↥H ℂ)
        = induce H (trivialIrreducibleCharacter ↥H : ClassFunction ↥H ℂ) := by
      rw [hc_spec φ, hcφ, htriv]
    have h0 := inner_induce_induce_trivial_eq_zero (H := H) hφ
    rw [← h1] at h0
    have h1' := inner_self_induce_eq_one_of_frobeniusGroup hF φ hφ
    rw [h0] at h1'
    exact zero_ne_one h1'
  -- Split the Burnside sum along the classifier fibers.
  have hsplit :
      ∑ φ ∈ Finset.univ.erase (trivialIrreducibleCharacter ↥H),
          ((φ : ClassFunction ↥H ℂ) 1) ^ 2
        = ∑ i ∈ Finset.univ.erase ind1H,
            ∑ φ ∈ (Finset.univ.erase (trivialIrreducibleCharacter ↥H)).filter
              (fun φ => c φ = i),
              ((φ : ClassFunction ↥H ℂ) 1) ^ 2 := by
    refine (Finset.sum_fiberwise_of_maps_to ?_ _).symm
    intro φ hφ
    rw [Finset.mem_erase] at hφ
    exact Finset.mem_erase.mpr ⟨hc_ne φ hφ.1, Finset.mem_univ _⟩
  -- Each fiber sums to `e · θ_i(1)²`.
  have hfiber_sum : ∀ i ∈ Finset.univ.erase ind1H,
      ∑ φ ∈ (Finset.univ.erase (trivialIrreducibleCharacter ↥H)).filter
          (fun φ => c φ = i),
          ((φ : ClassFunction ↥H ℂ) 1) ^ 2
        = (H.index : ℂ) * ((θ i : ClassFunction ↥H ℂ) 1) ^ 2 := by
    intro i hi
    rw [Finset.mem_erase] at hi
    -- The classifier fiber over `i ≠ ind1H` is the induction fiber of `θ i`.
    have hset : (Finset.univ.erase (trivialIrreducibleCharacter ↥H)).filter
        (fun φ => c φ = i)
        = Finset.univ.filter (fun φ : IrreducibleCharacter ↥H =>
            induce H (φ : ClassFunction ↥H ℂ) = induce H (θ i : ClassFunction ↥H ℂ)) := by
      ext φ
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨-, -⟩, hcφ⟩
        exact ⟨Finset.mem_univ _, by rw [hc_spec φ, hcφ]⟩
      · rintro ⟨-, hind⟩
        have hφ_ne : φ ≠ trivialIrreducibleCharacter ↥H := by
          intro h
          subst h
          -- `Ind 1 = Ind θ i` makes `⟨Ind 1, Ind θ i⟩` both `0` (trivial-vs-nontrivial)
          -- and `1` (Frobenius norm of `Ind θ i`).
          have h0 := inner_induce_trivial_induce_eq_zero (H := H) (hθ_ne i hi.1)
          rw [hind] at h0
          have h1' := inner_self_induce_eq_one_of_frobeniusGroup hF (θ i) (hθ_ne i hi.1)
          rw [h0] at h1'
          exact zero_ne_one h1'
        refine ⟨⟨hφ_ne, Finset.mem_univ _⟩, ?_⟩
        have := hc_spec φ
        rw [hind] at this
        exact hinj this.symm
    rw [hset]
    -- Degrees are constant on the fiber.
    have hdeg : ∀ φ ∈ Finset.univ.filter (fun φ : IrreducibleCharacter ↥H =>
        induce H (φ : ClassFunction ↥H ℂ) = induce H (θ i : ClassFunction ↥H ℂ)),
        ((φ : ClassFunction ↥H ℂ) 1) ^ 2 = ((θ i : ClassFunction ↥H ℂ) 1) ^ 2 := by
      intro φ hφ
      rw [Finset.mem_filter] at hφ
      have h1 := congrArg (fun f : ClassFunction G ℂ => f (1 : G)) hφ.2
      simp only [induce_apply_one] at h1
      have hidx : ((H.index : ℂ)) ≠ 0 := by
        rw [Nat.cast_ne_zero]
        exact Subgroup.index_ne_zero_of_finite
      have := mul_left_cancel₀ hidx h1
      rw [this]
    rw [Finset.sum_congr rfl hdeg, Finset.sum_const,
      card_induce_fiber_of_frobeniusGroup hF (θ i) (hθ_ne i hi.1), nsmul_eq_mul]
  calc (H.index : ℂ) * ∑ i ∈ Finset.univ.erase ind1H,
        ((θ i : ClassFunction ↥H ℂ) 1) ^ 2
      = ∑ i ∈ Finset.univ.erase ind1H,
          (H.index : ℂ) * ((θ i : ClassFunction ↥H ℂ) 1) ^ 2 := by
        rw [Finset.mul_sum]
    _ = ∑ φ ∈ Finset.univ.erase (trivialIrreducibleCharacter ↥H),
          ((φ : ClassFunction ↥H ℂ) 1) ^ 2 := by
        rw [hsplit]
        exact (Finset.sum_congr rfl hfiber_sum).symm
    _ = (Nat.card ↥H : ℂ) - 1 := sumNontrivialIrreducibleDegreeSq

end Frobenius

end OddOrder.RepresentationTheory

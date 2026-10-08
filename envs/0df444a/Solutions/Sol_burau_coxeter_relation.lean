-- Prove2me | solution 1 for burau_coxeter_relation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T01:01:15.524819+00:00
-- url     : https://prove2.me/submissions/730c6558-6077-4093-abba-513179617d7b

import Mathlib
import Definitions.Def_BurauFaithful_UnreducedBurau
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

set_option autoImplicit false

/-! The target (burau_coxeter_relation, 7d89c248) declares its own constants in its preamble.
A submission may not re-declare them under the same names (platform WA), so IDENTICAL
copies live under `P2MAlias.BurauNC` (bodies copied from the API bytes, `def` -> `abbrev`).
The statement refers to them as `BurauNC.liftS`, resolved through `open P2MAlias`.
The type-match gate checks `solution` against the real target up to unfolding. -/


namespace P2MAlias
namespace BurauNC

abbrev B3 := PresentedGroup (BraidsLinksMCG.braidRels 3)

abbrev g0 : B3 := BraidsLinksMCG.sigma (n := 3) ⟨0, by decide⟩

abbrev g1 : B3 := BraidsLinksMCG.sigma (n := 3) ⟨1, by decide⟩

abbrev Delta4 : B3 := (g0 * g1) ^ 6

abbrev Q : Type := B3 ⧸ Subgroup.normalClosure ({Delta4} : Set B3)

noncomputable abbrev q : B3 →* Q := QuotientGroup.mk' (Subgroup.normalClosure ({Delta4} : Set B3))

noncomputable abbrev liftS : Q := q (g0 ^ 2 * g1)

noncomputable abbrev liftT : Q := q g0⁻¹

end BurauNC
end P2MAlias

/-- If `x ^ 3 = y ^ 2` then `((x⁻¹ y)^3 (y⁻¹ x^2))^3 = x^6`. -/
theorem p2m7d89_key {G : Type*} [Group G] (x y : G) (h : x ^ 3 = y ^ 2) :
    ((x⁻¹ * y) ^ 3 * (y⁻¹ * x ^ 2)) ^ 3 = x ^ 6 := by
  calc ((x⁻¹ * y) ^ 3 * (y⁻¹ * x ^ 2)) ^ 3
        = x⁻¹ * y * x⁻¹ * y ^ 2 * x⁻¹ * y ^ 2 * x⁻¹ * y * x := by simp only [pow_succ, pow_zero, one_mul, _root_.mul_inv_rev] <;> group
    _ = x⁻¹ * y * x⁻¹ * x ^ 3 * x⁻¹ * x ^ 3 * x⁻¹ * y * x := by rw [← h]
    _ = x⁻¹ * y * x ^ 3 * y * x := by group
    _ = x⁻¹ * y * y ^ 2 * y * x := by rw [h]
    _ = x⁻¹ * (y ^ 2) ^ 2 * x := by group
    _ = x⁻¹ * (x ^ 3) ^ 2 * x := by rw [← h]
    _ = x ^ 6 := by group

/-- In any group, the braid relation `aba = bab` gives `(a^3 b)^3 = (ab)^6`. -/
theorem p2m7d89_braid {G : Type*} [Group G] (a b : G) (h : a * b * a = b * a * b) :
    (a ^ 3 * b) ^ 3 = (a * b) ^ 6 := by
  have hxy : (a * b) ^ 3 = (a * b * a) ^ 2 := by
    calc (a * b) ^ 3 = (a * b * a) * (b * a * b) := by simp only [pow_succ, pow_zero, one_mul, _root_.mul_inv_rev] <;> group
      _ = (a * b * a) * (a * b * a) := by rw [h]
      _ = (a * b * a) ^ 2 := by simp only [pow_succ, pow_zero, one_mul, _root_.mul_inv_rev] <;> group
  have hk := p2m7d89_key (a * b) (a * b * a) hxy
  have e1 : ((a * b)⁻¹ * (a * b * a)) ^ 3 * ((a * b * a)⁻¹ * (a * b) ^ 2) = a ^ 3 * b := by
    simp only [pow_succ, pow_zero, one_mul, _root_.mul_inv_rev] <;> group
  rw [e1] at hk
  exact hk

open P2MAlias in
theorem solution : (BurauNC.liftS⁻¹ * BurauNC.liftT) ^ 3 = 1 := by
  have hbr : BurauNC.g0 * BurauNC.g1 * BurauNC.g0 = BurauNC.g1 * BurauNC.g0 * BurauNC.g1 := by
    have hm := PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := BraidsLinksMCG.braidRels 3)
      (x := FreeGroup.of (⟨0, by decide⟩ : Fin (3 - 1)) * FreeGroup.of ⟨1, by decide⟩ *
        FreeGroup.of ⟨0, by decide⟩)
      (y := FreeGroup.of (⟨1, by decide⟩ : Fin (3 - 1)) * FreeGroup.of ⟨0, by decide⟩ *
        FreeGroup.of ⟨1, by decide⟩)
      (Or.inr ⟨⟨0, by decide⟩, ⟨1, by decide⟩, rfl, rfl⟩)
    simp only [map_mul] at hm
    exact hm
  have hk := p2m7d89_braid _ _ hbr
  have hD : BurauNC.q BurauNC.Delta4 = 1 :=
    (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure (Set.mem_singleton _))
  have e : ((BurauNC.g0 ^ 2 * BurauNC.g1)⁻¹ * BurauNC.g0⁻¹) ^ 3 =
      ((BurauNC.g0 ^ 3 * BurauNC.g1) ^ 3)⁻¹ := by simp only [pow_succ, pow_zero, one_mul, _root_.mul_inv_rev] <;> group
  have h1 : (BurauNC.liftS⁻¹ * BurauNC.liftT) ^ 3 =
      BurauNC.q (((BurauNC.g0 ^ 2 * BurauNC.g1)⁻¹ * BurauNC.g0⁻¹) ^ 3) := by
    simp only [BurauNC.liftS, BurauNC.liftT, map_pow, map_mul, map_inv]
  rw [h1, e, hk, map_inv]
  change (BurauNC.q BurauNC.Delta4)⁻¹ = 1
  rw [hD, inv_one]

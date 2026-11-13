-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.card_modEq_one_of_prime_normalizing_fpf
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:26:42.794677+00:00
-- url     : https://prove2.me/submissions/de04cb28-ec25-4085-aa26-27039f929142

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupMCore.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupMCore

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupMCore.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- **Fixed-point-free congruence** (the mod-`p` analogue of the `U⋊W₁` Frobenius congruence,
group-theoretic core).  If a subgroup `A` of prime order `p` normalizes a finite group `U` and
acts on it fixed-point-freely by conjugation, then `|U| ≡ 1 (mod p)`.  The conjugation action of
the `p`-group `A` on `U` has `{1}` as its only fixed point, so the `p`-group fixed-point
congruence `Nat.card U ≡ Nat.card (fixedPoints) (mod p)` gives `|U| ≡ 1 (mod p)`. -/
theorem _root_.solution {G : Type*} [Group G] [Finite G]
    {U A : Subgroup G} {p : ℕ} (hp : p.Prime) (hA_card : Nat.card ↥A = p)
    (hA_norm : A ≤ Subgroup.normalizer (U : Set G))
    (hfpf : ∀ a ∈ A, a ≠ 1 → ∀ u ∈ U, u ≠ 1 → (a : G) * u * (a : G)⁻¹ ≠ u) :
    Nat.card ↥U ≡ 1 [MOD p] := by
  let : MulAction ↥A ↥U := MulAction.compHom ↥U (Subgroup.inclusion hA_norm)
  have hpg : IsPGroup p ↥A := IsPGroup.of_card (by rw [hA_card, pow_one])
  -- the conjugation `smul` is `a • u = a u a⁻¹`
  have hsmul : ∀ (a : ↥A) (u : ↥U), ((a • u : ↥U) : G) = (a : G) * (u : G) * (a : G)⁻¹ := by
    intro a u; rfl
  -- the only fixed point is `1`
  have : Nontrivial ↥A :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hA_card]; exact hp.one_lt)
  obtain ⟨a0, ha0⟩ := exists_ne (1 : ↥A)
  have ha0G : (a0 : G) ≠ 1 := fun h => ha0 (Subtype.ext h)
  have hfix_eq : MulAction.fixedPoints ↥A ↥U = {(1 : ↥U)} := by
    ext u
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hu
      by_contra hune
      have huG : (u : G) ≠ 1 := fun h => hune (Subtype.ext h)
      have hfixa : ((a0 • u : ↥U) : G) = (u : G) :=
        congrArg (Subtype.val) (hu a0)
      rw [hsmul] at hfixa
      exact hfpf (a0 : G) a0.2 ha0G (u : G) u.2 huG hfixa
    · rintro rfl
      intro a
      apply Subtype.ext
      rw [hsmul]
      simp
  have hfix_card : Nat.card (MulAction.fixedPoints ↥A ↥U) = 1 := by
    rw [hfix_eq]
    have := Set.uniqueSingleton (1 : ↥U)
    exact Nat.card_unique
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have hcong := hpg.card_modEq_card_fixedPoints (α := ↥U)
  rwa [hfix_card] at hcong

end OddOrder.Peterfalvi.S16

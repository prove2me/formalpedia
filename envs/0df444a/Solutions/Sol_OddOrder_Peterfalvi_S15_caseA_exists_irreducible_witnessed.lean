-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.caseA_exists_irreducible_witnessed
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:08:38.106547+00:00
-- url     : https://prove2.me/submissions/f699cec6-2bc6-4620-9348-0d8fb65dbb42

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_CharacterDegreeSupply.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeSupply

-- ===== OddOrder/Peterfalvi/S15_CharacterDegreeSupply.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
/-- **(9.8.c) with the regular seed exposed**: the degree-`qu` irreducible member of `𝒮(H₀C)` from
Peterfalvi (9.8.c) is `Ind_{HU}^M(Ind_{HC}(hcPsi θ))` for a *regular* seed `θ` (nontrivial on every
Clifford summand `caseA.Hpart i`, hence `θ ≠ 1`).  Identical parity argument to
`caseA_exists_irreducible_sOf_H0C` (`exists_regular_not_reducible_of_odd` on `Xθ \ Xmu`,
`|Xμ| = p-1`, `u·|Xθ| = (p-1)^q`, `u` odd, `p-1` even), but returns the *witnessing* `θ` (needed to
recover the `Ind_{HC}(linear)` shape and route it through `isIndHC_of_source_eq_induce_hcPsi` to a
`LambdaWitness`; the bare existence hides `θ`). -/
theorem _root_.solution [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    [Finite ((↥data.H ⧸ chief.N) →* ℂˣ)]
    [Finite ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal] :
    ∃ θ : (↥data.H ⧸ chief.N) →* ℂˣ, θ ≠ 1 ∧
      (∀ i, θ.comp (caseA.Hpart i).subtype ≠ 1) ∧
      IsIrreducibleCharacter (induceHU data (ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsi chief θ).toClassFunction)) := by
  classical
  have : Fintype ((↥data.H ⧸ chief.N) →* ℂˣ) := Fintype.ofFinite _
  have : Fintype ↥(hInHu data) := Fintype.ofFinite _
  have : Fintype
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :=
    Fintype.ofFinite _
  let : Fintype ↥M := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hq : 0 < data.q := data.nontrivial.2.1.pos
  have hpq : chief.p ^ data.q ∣ Nat.card ↥data.H := ⟨Nat.card ↥chief.H0, chief.quotient_order⟩
  have hp_dvd : chief.p ∣ Nat.card G :=
    (dvd_pow_self chief.p hq.ne').trans (hpq.trans (Subgroup.card_subgroup_dvd_card data.H))
  have hp_ne2 : chief.p ≠ 2 := fun h =>
    (Nat.not_even_iff_odd.mpr hG.odd) (even_iff_two_dvd.mpr (h ▸ hp_dvd))
  have hp1_even : Even (chief.p - 1) := by
    obtain ⟨k, hk⟩ := chief.p_prime.odd_of_ne_two hp_ne2
    exact ⟨k, by omega⟩
  set RegF := Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ =>
    ∀ i, θ.comp (caseA.Hpart i).subtype ≠ 1 with hRegF
  set Xθ := RegF.image fun θ =>
      ClassFunction.induce (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
        M).subgroupOf (huSub data)) (hcPsi chief θ).toClassFunction with hXθ
  set Xmu := Xθ.filter fun ζ => ¬ IsIrreducibleCharacter (induceHU data ζ) with hXmu
  have hcard : (↑Xmu : Set (ClassFunction ↥(huSub data) ℂ)).ncard = chief.p - 1 := by
    rw [Set.ncard_coe_finset]; exact caseA_Xmu_card_eq caseA hG
  have hcount : chars.u * (↑Xθ : Set (ClassFunction ↥(huSub data) ℂ)).ncard
      = (chief.p - 1) ^ data.q := by
    rw [Set.ncard_coe_finset]; exact oXtheta_count caseA
  obtain ⟨ζ, hζ, hζn⟩ := exists_regular_not_reducible_of_odd Xθ.finite_toSet
    (Finset.coe_subset.mpr (Finset.filter_subset _ _)) hcard hcount
    (Nat.sub_pos_of_lt chief.p_prime.one_lt) hp1_even (u_odd hG chars) data.nontrivial.2.1.two_le
  rw [Finset.mem_coe, hXθ, Finset.mem_image] at hζ
  obtain ⟨θ, hθ, rfl⟩ := hζ
  have hreg := (Finset.mem_filter.mp hθ).2
  have hnt : θ ≠ 1 := fun h => hreg ⟨0, hq⟩ (by rw [h]; exact MonoidHom.one_comp _)
  refine ⟨θ, hnt, hreg, ?_⟩
  by_contra h
  refine hζn ?_
  simp only [Finset.mem_coe, Finset.mem_filter, hXθ, Finset.mem_image]
  exact ⟨⟨θ, hθ, rfl⟩, h⟩

end OddOrder.Peterfalvi.S15

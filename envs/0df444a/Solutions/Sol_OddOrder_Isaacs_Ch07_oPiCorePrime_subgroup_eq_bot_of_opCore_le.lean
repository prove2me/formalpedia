-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.oPiCorePrime_subgroup_eq_bot_of_opCore_le
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:52:08.59506+00:00
-- url     : https://prove2.me/submissions/00c42f4c-3c4a-4e88-85f2-3f87371ca2ce

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ_Setup.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJClose.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B1_NormalJ_Setup
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJClose

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ_Setup.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Isaacs Thm 7.6 Step 1** (mmd L3837): Hall-Higman 3.21 with `π = {p}`.

If `G` is `{p}`-separable (equivalently `p`-solvable) and `O_{p'}(G) = ⊥`,
then `C_G(O_p(G)) ≤ O_p(G)`. -/
theorem centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥) :
    Subgroup.centralizer (OddOrder.Isaacs.Ch01.opCore p G : Set G) ≤
      OddOrder.Isaacs.Ch01.opCore p G := by
  have hπ' : OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G = ⊥ := by
    rw [show ({q | q ∉ ({p} : Set ℕ)} : Set ℕ) = {q | q ≠ p} by
      ext q; simp]
    exact hOp'
  have hHH :=
    OddOrder.Isaacs.Ch03.hall_higman_1_2_3 (G := G) ({p} : Set ℕ) hπ'
  rw [OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p] at hHH
  exact hHH

end OddOrder.Isaacs.Ch07

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJClose.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Isaacs Thm 7.6 Step 1(b)** (mmd L3843): if `U = O_p(G) ≤ H ≤ G` then
`O_{p'}(H) = 1`.

Book argument: write `M = O_{p'}(H)`.  Both `M` and `U` (as `U.subgroupOf H`)
are normal `H`-subgroups with coprime orders (`M` a `p'`-group, `U` a `p`-group),
so they commute; hence `M` (mapped into `G`) lies in `C_G(U) ≤ U` (Hall-Higman
3.21, hypothesis (iv)).  But `M` is a `p'`-group inside the `p`-group `U`, so
`M = 1`. -/
theorem _root_.solution
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    {H : Subgroup G} (hUH : OddOrder.Isaacs.Ch01.opCore p G ≤ H) :
    OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} (↥H) = ⊥ := by
  classical
  set U : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hU_def
  set M : Subgroup (↥H) := OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} (↥H) with hM_def
  -- `M` is a `{q ≠ p}`-group.
  have hM_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ≠ p} M :=
    OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (G := ↥H) {q | q ≠ p}
  -- `U` lives inside `H` as `U.subgroupOf H = U.comap H.subtype`, normal in `↥H`.
  have hU_le_H : U ≤ H := hUH
  set Usub : Subgroup (↥H) := U.subgroupOf H with hUsub_def
  have hUsub_normal : Usub.Normal :=
    (OddOrder.Isaacs.Ch01.opCore.normal p G).subgroupOf H
  -- `Usub` is a `p`-group (`comap` of the `p`-group `U` along an injective hom).
  have hU_pg : IsPGroup p ↥U := OddOrder.Isaacs.Ch01.opCore_isPGroup p G
  have hUsub_pg : IsPGroup p ↥Usub := hU_pg.comap_subtype
  obtain ⟨k, hUsub_card⟩ : ∃ k, Nat.card ↥Usub = p ^ k := IsPGroup.iff_card.mp hUsub_pg
  -- `M ⊓ Usub = ⊥`: coprime cards (`p ∤ |M|` since `M` is `{q≠p}`).
  have hp_not_dvd_M : ¬ p ∣ Nat.card M := by
    intro hdvd
    have hp_pf : p ∈ (Nat.card M).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩
    exact (hM_pi p hp_pf) rfl
  have hcoprime : Nat.Coprime (Nat.card M) (Nat.card ↥Usub) := by
    rw [hUsub_card]
    have hp_cop : Nat.Coprime p (Nat.card M) :=
      (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp_not_dvd_M
    exact (hp_cop.symm).pow_right k
  have h_disj : Disjoint M Usub := Subgroup.disjoint_of_coprime_natCard hcoprime
  -- `M` commutes with `Usub` (both normal, disjoint).
  have h_comm : ∀ m ∈ M, ∀ u ∈ Usub, (m : ↥H) * u = u * m := fun m hm u hu =>
    Subgroup.commute_of_normal_of_disjoint M Usub
      (OddOrder.Isaacs.Ch03.oPiCore.normal {q | q ≠ p} (↥H)) hUsub_normal h_disj
      m u hm hu
  -- Map `M` into `G`.
  set M' : Subgroup G := M.map H.subtype with hM'_def
  -- `M' ≤ C_G(U)`.
  have hM'_le_centralizer : M' ≤ Subgroup.centralizer (U : Set G) := by
    rintro _ ⟨m, hm, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu_H : u ∈ H := hU_le_H hu
    have hu_Usub : (⟨u, hu_H⟩ : ↥H) ∈ Usub := by
      rw [hUsub_def, Subgroup.mem_subgroupOf]; exact hu
    have hval := congrArg (Subtype.val : ↥H → G) (h_comm m hm ⟨u, hu_H⟩ hu_Usub)
    simpa using hval.symm
  -- `C_G(U) ≤ U` (Hall-Higman) ⇒ `M' ≤ U`.
  have hM'_le_U : M' ≤ U := hM'_le_centralizer.trans
    (centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot h_oPiPrime_trivial)
  -- `M'` is a `p`-group (inside `U`) and `Nat.card M' = Nat.card M` (injective map);
  -- but `p ∤ Nat.card M`, so `Nat.card M' = 1`, hence `M' = ⊥`, hence `M = ⊥`.
  have hM'_card : Nat.card ↥M' = Nat.card M := by
    rw [hM'_def]
    exact Nat.card_congr (Subgroup.equivMapOfInjective M H.subtype
        Subtype.coe_injective).symm.toEquiv
  have hM'_pg : IsPGroup p ↥M' :=
    hU_pg.of_injective (Subgroup.inclusion hM'_le_U) (Subgroup.inclusion_injective hM'_le_U)
  obtain ⟨j, hj⟩ : ∃ j, Nat.card ↥M' = p ^ j := IsPGroup.iff_card.mp hM'_pg
  have hj_zero : j = 0 := by
    by_contra hj_ne
    apply hp_not_dvd_M
    rw [← hM'_card, hj]
    exact dvd_pow_self p hj_ne
  have hM'_card_one : Nat.card ↥M' = 1 := by rw [hj, hj_zero, pow_zero]
  have hM'_bot : M' = ⊥ := Subgroup.card_eq_one.mp hM'_card_one
  -- `M.map H.subtype = ⊥` with injective `H.subtype` ⇒ `M = ⊥`.
  have hM_le_ker : M ≤ (H.subtype).ker := by
    rw [← Subgroup.map_eq_bot_iff]; exact hM'_bot
  rw [Subgroup.ker_subtype] at hM_le_ker
  exact le_bot_iff.mp hM_le_ker

end OddOrder.Isaacs.Ch07

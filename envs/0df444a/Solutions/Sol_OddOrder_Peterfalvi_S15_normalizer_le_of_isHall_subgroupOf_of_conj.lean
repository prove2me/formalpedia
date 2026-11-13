-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.normalizer_le_of_isHall_subgroupOf_of_conj
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:11:04.163673+00:00
-- url     : https://prove2.me/submissions/3dae923b-8eae-4b25-8c0b-673fac261042

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndTBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

-- ===== OddOrder/Peterfalvi/S15_SAndTBasic.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Structural core of Peterfalvi (13.17.a)** — the `L`-conjugate-to-`S` exclusion.  If `U` is a
`π`-Hall subgroup of the solvable subgroup `V`, `L` is conjugate to `V` (`L^g = V`, i.e.
`conj g • L = V`), and `N_G(U) ⊆ L`, then `N_G(U) ⊆ V`.

*Proof (Pf p.81):* `U ⊆ N_G(U) ⊆ L`, so `U^g = conj g • U ⊆ conj g • L = V` is another
`π`-Hall subgroup of `V` (same order as `U`).  Since `V` is solvable, Hall conjugacy
(`exists_conj_eq_of_isHall_subgroupOf`, Isaacs Thm 3.21) gives `w ∈ V` with `(U^g)^w = U`, i.e.
`wg ∈ N_G(U)`.  Then `N_G(U) = N_G(U)^{wg} ⊆ L^{wg} = (L^g)^w = V^w = V`.  Specialised to
`V = S` of type II (with `hNUS = IsTypeII.normalizer_not_le` transferred to `U`) this rules out
the `L ~ S` branch of (8.8.b4).  Generic and reusable; the only `S`-specific input is "`U` is a
Hall subgroup of `S`". -/
theorem _root_.solution [Finite G] {V U L : Subgroup G}
    (hVsolv : Group.IsSolvable ↥V) (hUV : U ≤ V) {π : Set ℕ}
    (hUhall : Ch03.IsHallSubgroup π (U.subgroupOf V))
    {g : G} (hconj : MulAut.conj g • L = V)
    (hNUL : Subgroup.normalizer (U : Set G) ≤ L) :
    Subgroup.normalizer (U : Set G) ≤ V := by
  -- `U ⊆ L`, hence `U^g = conj g • U ⊆ conj g • L = V`.
  have hUL : U ≤ L := Subgroup.le_normalizer.trans hNUL
  have hUgV : (MulAut.conj g • U : Subgroup G) ≤ V := by
    rw [← hconj]; exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hUL
  -- `U^g` is a `π`-Hall subgroup of `V`: same card and (hence) same index in `V` as `U`.
  have hcardUg : Nat.card ↥(MulAut.conj g • U : Subgroup G) = Nat.card ↥U := by
    rw [OddOrder.BG.Ch3.S12.mulAut_smul_eq_map]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hcardEq : Nat.card ↥((MulAut.conj g • U).subgroupOf V)
      = Nat.card ↥(U.subgroupOf V) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUgV).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUV).toEquiv, hcardUg]
  have hidxEq : ((MulAut.conj g • U).subgroupOf V).index = (U.subgroupOf V).index := by
    have h1 := Subgroup.card_mul_index ((MulAut.conj g • U).subgroupOf V)
    have h2 := Subgroup.card_mul_index (U.subgroupOf V)
    rw [hcardEq] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
  have hUghall : Ch03.IsHallSubgroup π ((MulAut.conj g • U).subgroupOf V) :=
    ⟨fun p hp => hUhall.1 p (hcardEq ▸ hp), fun p hp => hUhall.2 p (hidxEq ▸ hp)⟩
  -- Hall conjugacy in the solvable `V`: some `w ∈ V` conjugates `U^g` back to `U`.
  obtain ⟨w, hwV, hw⟩ :=
    OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf hVsolv hUgV hUV hUghall hUhall
  -- `wg` normalises `U`, and conjugates `L` onto `V`.
  have hwgU : MulAut.conj (w * g) • U = U := by rw [map_mul, mul_smul, hw]
  have hLconj : MulAut.conj (w * g) • L = V := by
    rw [map_mul, mul_smul, hconj]
    exact conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hwV)
  -- `N_G(U) = N_G(U)^{wg} ⊆ L^{wg} = V`.
  calc Subgroup.normalizer (U : Set G)
      = MulAut.conj (w * g) • Subgroup.normalizer (U : Set G) := by
        rw [OddOrder.BG.Ch3.S12.normalizer_conj_smul, hwgU]
    _ ≤ MulAut.conj (w * g) • L := Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hNUL
    _ = V := hLconj

end OddOrder.Peterfalvi.S15

-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.coprime_card_U_card_P_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:09:06.734056+00:00
-- url     : https://prove2.me/submissions/1983063a-370a-4e68-9cb6-dab8b8bdb1d1

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndTDefs.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

-- ===== OddOrder/Peterfalvi/S15_SAndTDefs.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Coprimality of the configuration complement from disjointness** (the Hall mechanism of
Phase 0): for `S` of type II, if the complement `U` meets the Fitting kernel `P = S_F` trivially
(`P ⊓ U = ⊥`), then `|U|` is coprime to `|P|`.

This is the *derivable* half of the (13.2) faithfulness datum.
`P = S_F = maxNilpotentNormalHall M'`
(`TypeIIData.derived_fitting_eq`) is a **relative Hall** subgroup of `M' = derivedInG S`
(`maxNilpotentNormalHall_isHall`: `(M_F).subgroupOf M'` is Hall in `↥M'`), so `|P|` is coprime to
its
index `[M' : P]`. Disjointness plus `M' = P ⊔ U` (`S_deriv_eq_PU`) makes `U` a genuine
`P`-complement
with `|U| = [M' : P]`, whence `Coprime |U| |P|`.  The remaining input `P ⊓ U = ⊥` is the carrier
faithfulness datum (`hyp.U` is currently under-constrained; supplied by the enriched §16 Hypothesis,
Phase 0(b)).  Composes with `exists_conj_typeP_U_of_coprime` to discharge the L~S rule-out. -/
theorem _root_.solution [Finite G]
    (hyp : Hypothesis (G := G)) (tdata : TypeIIData hyp.S) (hdisj : hyp.P ⊓ hyp.U = ⊥) :
    Nat.Coprime (Nat.card ↥hyp.U) (Nat.card ↥hyp.P) := by
  have hPH : hyp.P = tdata.typeP.H := by rw [hyp.P_eq_SF, tdata.typeP.H_eq]
  have hP_le : hyp.P ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_left
  have hU_le : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
  have hM'_le_S : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hS_le_NP : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  have hPn_normal : (hyp.P.subgroupOf (derivedInG hyp.S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le).mpr (hM'_le_S.trans hS_le_NP)
  -- `U` complements `P` in `M'` (disjoint from `hdisj`, join from `S_deriv_eq_PU`).
  have hPnUn_inf : (hyp.P.subgroupOf (derivedInG hyp.S)) ⊓
      (hyp.U.subgroupOf (derivedInG hyp.S)) = ⊥ := by
    ext ⟨x, hx⟩
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subtype.ext_iff,
      OneMemClass.coe_one]
    refine ⟨fun ⟨hxP, hxU⟩ => ?_, fun h => by simp [h]⟩
    have hxPU : x ∈ (hyp.P ⊓ hyp.U : Subgroup G) := ⟨hxP, hxU⟩
    rwa [hdisj, Subgroup.mem_bot] at hxPU
  have hPnUn_sup : (hyp.P.subgroupOf (derivedInG hyp.S)) ⊔
      (hyp.U.subgroupOf (derivedInG hyp.S)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hP_le hU_le, hyp.S_deriv_eq_PU.symm, Subgroup.subgroupOf_self]
  have hUcompl : (hyp.P.subgroupOf (derivedInG hyp.S)).IsComplement'
      (hyp.U.subgroupOf (derivedInG hyp.S)) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hPnUn_inf)
    have hmul := Subgroup.normal_mul (hyp.P.subgroupOf (derivedInG hyp.S))
      (hyp.U.subgroupOf (derivedInG hyp.S))
    rw [hPnUn_sup, Subgroup.coe_top] at hmul
    exact hmul.symm
  have hidx : (hyp.P.subgroupOf (derivedInG hyp.S)).index = Nat.card ↥hyp.U := by
    rw [hUcompl.symm.index_eq_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU_le).toEquiv]
  -- `P` is a relative Hall subgroup of `M'`, so `|P|` is coprime to `[M' : P] = |U|`.
  have hP_mnh : hyp.P = maxNilpotentNormalHall (derivedInG hyp.S) :=
    hPH.trans tdata.derived_fitting_eq.symm
  have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall (derivedInG hyp.S)
  rw [← hP_mnh] at hHall
  have hcop_idx := hHall.coprime_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le).toEquiv, hidx] at hcop_idx
  exact hcop_idx.symm

end OddOrder.Peterfalvi.S15

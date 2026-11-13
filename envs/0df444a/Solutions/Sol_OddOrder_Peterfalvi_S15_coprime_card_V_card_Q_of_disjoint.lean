-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.coprime_card_V_card_Q_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:10:31.508445+00:00
-- url     : https://prove2.me/submissions/c6540f03-c0cb-4194-90c1-5e94ab0bbbdf

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

/-- **`T`-side dual of `coprime_card_U_card_P_of_disjoint`** (Pf (13.2.a), V-side): for the type-II
member `T` with a `TypeIIData` witness `tdata` and `Q ⊓ V = ⊥`, the complement order `|V|` is
coprime to `|Q| = |T_F|`.  The `V`-side analogue used by the V-side of (13.17)/(14.10). -/
theorem _root_.solution [Finite G]
    (hyp : Hypothesis (G := G)) (tdata : TypeIIData hyp.T) (hdisj : hyp.Q ⊓ hyp.V = ⊥) :
    Nat.Coprime (Nat.card ↥hyp.V) (Nat.card ↥hyp.Q) := by
  have hQH : hyp.Q = tdata.typeP.H := by rw [hyp.Q_eq_TF, tdata.typeP.H_eq]
  have hQ_le : hyp.Q ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_left
  have hV_le : hyp.V ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_right
  have hM'_le_T : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have hT_le_NQ : hyp.T ≤ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
  have hQn_normal : (hyp.Q.subgroupOf (derivedInG hyp.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le).mpr (hM'_le_T.trans hT_le_NQ)
  have hQnVn_inf : (hyp.Q.subgroupOf (derivedInG hyp.T)) ⊓
      (hyp.V.subgroupOf (derivedInG hyp.T)) = ⊥ := by
    ext ⟨x, hx⟩
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subtype.ext_iff,
      OneMemClass.coe_one]
    refine ⟨fun ⟨hxQ, hxV⟩ => ?_, fun h => by simp [h]⟩
    have hxQV : x ∈ (hyp.Q ⊓ hyp.V : Subgroup G) := ⟨hxQ, hxV⟩
    rwa [hdisj, Subgroup.mem_bot] at hxQV
  have hQnVn_sup : (hyp.Q.subgroupOf (derivedInG hyp.T)) ⊔
      (hyp.V.subgroupOf (derivedInG hyp.T)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQ_le hV_le, hyp.T_deriv_eq_QV.symm, Subgroup.subgroupOf_self]
  have hVcompl : (hyp.Q.subgroupOf (derivedInG hyp.T)).IsComplement'
      (hyp.V.subgroupOf (derivedInG hyp.T)) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hQnVn_inf)
    have hmul := Subgroup.normal_mul (hyp.Q.subgroupOf (derivedInG hyp.T))
      (hyp.V.subgroupOf (derivedInG hyp.T))
    rw [hQnVn_sup, Subgroup.coe_top] at hmul
    exact hmul.symm
  have hidx : (hyp.Q.subgroupOf (derivedInG hyp.T)).index = Nat.card ↥hyp.V := by
    rw [hVcompl.symm.index_eq_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV_le).toEquiv]
  have hQ_mnh : hyp.Q = maxNilpotentNormalHall (derivedInG hyp.T) :=
    hQH.trans tdata.derived_fitting_eq.symm
  have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall (derivedInG hyp.T)
  rw [← hQ_mnh] at hHall
  have hcop_idx := hHall.coprime_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le).toEquiv, hidx] at hcop_idx
  exact hcop_idx.symm

end OddOrder.Peterfalvi.S15

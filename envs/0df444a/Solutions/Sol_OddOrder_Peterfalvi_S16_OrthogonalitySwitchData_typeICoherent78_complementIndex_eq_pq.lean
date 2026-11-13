-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.OrthogonalitySwitchData.typeICoherent78_complementIndex_eq_pq
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:36:23.372512+00:00
-- url     : https://prove2.me/submissions/8eec79cd-4c48-43ce-a34a-295e04613447

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_PairingBessel.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/ComparingLMBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_BetaVanishing

-- ===== OddOrder/Peterfalvi/S16_PairingBessel.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S09

open OddOrder.Peterfalvi.S09.Cert

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

namespace TypeICoherent78Data

variable [Finite G] {L : Subgroup G} (data : TypeICoherent78Data L)

variable (hG : OddOrder.BG.IsMinimalSimpleOdd G)

/-- `h = |H|` (bundle form). -/
theorem kernelOrder_eq :
    (data.h78 hG).kernelOrder = Nat.card ↥data.kernelIn := by
  rw [show (data.h78 hG).kernelOrder = Nat.card data.kernel from rfl]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.kernel_le).toEquiv).symm

end TypeICoherent78Data

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/ComparingLMBasic.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

namespace OrthogonalitySwitchData

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`e_L = |L : H_L| = p q`** for the (14.3) L-side.  The (7.8) complement index
`complementIndex = [L : kernelIn]` of *any* coherence bundle `dataL` on `L` equals the order of
the (14.3) Frobenius complement of `L` (`Ldata.typeI_data.frobenius`), because both complement the
*same* canonical kernel `H_L = maxNilpotentNormalHall L` (`kernel_le`/`typeF.H_eq`), so both have
order `[L : H_L]`.  That complement has order `p q` by (14.3) `typeI_complement_card_eq_pq`. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (Ldata : LHypothesis hyp) (dataL : TypeICoherent78Data Ldata.L) :
    (dataL.h78 hG).complementIndex = hyp.base.p * hyp.base.q := by
  have := dataL.kernelIn_normal
  have hLeq : Ldata.typeI_data.L = Ldata.L := Ldata.typeI_data_L_eq
  -- `complementIndex = |dataL.C|` (Frobenius complement of `kernelIn`).
  have hcomplD : Nat.card ↥dataL.kernelIn * Nat.card ↥dataL.C = Nat.card ↥Ldata.L :=
    dataL.hFrob.isComplement.card_mul_card
  have hce : (dataL.h78 hG).complementIndex = Nat.card ↥dataL.C := by
    change Nat.card ↥Ldata.L / Nat.card dataL.kernel = Nat.card ↥dataL.C
    rw [show Nat.card dataL.kernel = Nat.card ↥dataL.kernelIn from
        (dataL.kernelOrder_eq hG) ▸ rfl,
      ← hcomplD, Nat.mul_div_cancel_left _ Nat.card_pos]
  -- `|kernelIn| · |Ldata-complement| = |L|` (the (14.3) Frobenius package), after transporting
  -- the cards from the ambient `typeI_data.L` to `L` and identifying the canonical kernel.
  have hcomplL0 :=
    Ldata.typeI_data.frobenius.frobenius.isComplement.card_mul_card
  have hkerDeq : dataL.kernel = maxNilpotentNormalHall Ldata.L := by
    rw [show dataL.kernel = dataL.typeIHyp.typeI.typeF.H from rfl,
      dataL.typeIHyp.typeI.typeF.H_eq]
  have hkercard : Nat.card ↥((Ldata.typeI_data.frobenius.typeI.typeF.H).subgroupOf
        Ldata.typeI_data.L)
      = Nat.card ↥dataL.kernelIn := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        Ldata.typeI_data.frobenius.typeI.typeF.H_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe dataL.kernel_le).toEquiv,
      hkerDeq, Ldata.typeI_data.frobenius.typeI.typeF.H_eq, hLeq]
  have hLcard : Nat.card ↥Ldata.typeI_data.L = Nat.card ↥Ldata.L := by rw [hLeq]
  have hcomplL : Nat.card ↥dataL.kernelIn
      * Nat.card ↥Ldata.typeI_data.frobenius.complement = Nat.card ↥Ldata.L := by
    rw [← hkercard, ← hLcard]; exact hcomplL0
  -- hence `|dataL.C| = |Ldata-complement| = p q`.
  have hCeq : Nat.card ↥dataL.C = Nat.card ↥Ldata.typeI_data.frobenius.complement :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (hcomplD.trans hcomplL.symm)
  rw [hce, hCeq]
  exact Ldata.typeI_complement_card_eq_pq

end OrthogonalitySwitchData

end OddOrder.Peterfalvi.S16

-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.TypeIOverNormalizerData.prime_dvd_sq_sub_one_of_omega1Center
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:10:59.303169+00:00
-- url     : https://prove2.me/submissions/fa09121c-eb31-4ca1-b0bb-3833e202231d

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_CaseAOmegaFixedPointFree.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

-- ===== OddOrder/Peterfalvi/S15_CaseAOmegaFixedPointFree.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

/-- **Peterfalvi (14.6), fixed-point-free center-layer count.**  Let `L = H ⋊ C` be a
Frobenius group in the ambient group `G`, and let `R ≤ H`.  If a subgroup `A ≤ L`
of prime order `p` meets `H` trivially and normalizes `R`, then it also normalizes
`Ω₁(Z(R))`.  When that center layer has order `r` or `r²`, Frobenius orbit counting
gives `p ∣ r² - 1`.

This is the reusable ambient form of the `nR1W2y` / `regR1W2y` step in the Coq
formalization of (14.6). -/
theorem prime_dvd_sq_sub_one_of_frobenius_omega1Center [Finite G]
    {L H R A : Subgroup G} {p r : ℕ}
    (hp : p.Prime) (hr : r.Prime)
    (hHL : H ≤ L)
    (hFrobL : ∃ C : Subgroup ↥L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (H.subgroupOf L) C)
    (hRH : R ≤ H)
    (hcard :
      Nat.card ↥(OddOrder.BG.Ch3.S10.omega1CenterInG R r) = r ∨
        Nat.card ↥(OddOrder.BG.Ch3.S10.omega1CenterInG R r) = r ^ 2)
    (hAL : A ≤ L) (hAH : A ⊓ H = ⊥)
    (hAcard : Nat.card ↥A = p)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) :
    p ∣ r ^ 2 - 1 := by
  let R1 : Subgroup G := OddOrder.BG.Ch3.S10.omega1CenterInG R r
  have hR1H : R1 ≤ H :=
    (OddOrder.BG.Ch3.S10.omega1CenterInG_le R r).trans hRH
  have hR1card_gt : 1 < Nat.card ↥R1 := hcard.elim
    (fun h => by simpa only [R1, h] using hr.one_lt)
    (fun h => by rw [show Nat.card ↥R1 = r ^ 2 from h]; nlinarith [hr.one_lt])
  have hR1ne : R1 ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hR1card_gt
    exact (lt_irrefl 1 hR1card_gt)
  have hAne : A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hAcard
    have := hp.one_lt
    omega
  have hAR1 : A ≤ Subgroup.normalizer (R1 : Set G) :=
    hAR.trans (OddOrder.BG.Ch3.S10.normalizer_le_normalizer_omega1CenterInG R r)
  have hmod :=
    OddOrder.GroupTheory.IsFrobeniusGroup.card_modEq_one_of_invariant_le_kernel_ambient
      hHL hFrobL hR1H hR1ne hAL hAH hAne hAR1
  rw [hAcard] at hmod
  have hpdvd : p ∣ Nat.card ↥R1 - 1 :=
    (Nat.modEq_iff_dvd' Nat.card_pos).mp hmod.symm
  rcases hcard with hcard | hcard
  · have hpr : p ∣ r - 1 := by rwa [show Nat.card ↥R1 = r from hcard] at hpdvd
    have hfac : r ^ 2 - 1 = (r + 1) * (r - 1) := by
      rw [sq]
      exact mul_self_tsub_one r
    exact hpr.trans (by rw [hfac]; exact dvd_mul_left _ _)
  · rwa [show Nat.card ↥R1 = r ^ 2 from hcard] at hpdvd

/-- **Peterfalvi (14.6), `W₂^y` acts fixed-point-freely on `Ω₁(Z(R))`.**  For the
type-I maximal subgroup `L` over `N_G(U)` supplied by (13.17)/(14.5), let `R` be a
Sylow `r`-subgroup of its Fitting kernel `H`.  The (14.5) conjugate `W₂^y` lies in
the Frobenius complement, has order `p`, and normalizes `R` because `H` is
nilpotent.  Thus the preceding counting theorem gives `p ∣ r² - 1` whenever
`|Ω₁(Z(R))|` is `r` or `r²`. -/
theorem _root_.solution [Finite G]
    {hyp : Hypothesis (G := G)} (data : TypeIOverNormalizerData hyp)
    {r : ℕ} (hr : r.Prime) (R : Sylow r ↥data.H)
    (hcard :
      Nat.card ↥(OddOrder.BG.Ch3.S10.omega1CenterInG
        ((R : Subgroup ↥data.H).map data.H.subtype) r) = r ∨
      Nat.card ↥(OddOrder.BG.Ch3.S10.omega1CenterInG
        ((R : Subgroup ↥data.H).map data.H.subtype) r) = r ^ 2) :
    hyp.p ∣ r ^ 2 - 1 := by
  classical
  let : Fact r.Prime := ⟨hr⟩
  let Rg : Subgroup G := (R : Subgroup ↥data.H).map data.H.subtype
  have hHL : data.H ≤ data.L := by
    rw [data.H_eq_LF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le data.L
  have hkernel : data.frobenius.typeI.typeF.H = data.H := by
    rw [data.frobenius.typeI.typeF.H_eq, ← data.H_eq_LF]
  have hFrobL : ∃ C : Subgroup ↥data.L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥data.L
        (data.H.subgroupOf data.L) C := by
    refine ⟨data.frobenius.complement, ?_⟩
    rw [← hkernel]
    exact data.frobenius.frobenius
  obtain ⟨y, _hyQ, hyA⟩ := data.exists_y_W2_conj_le_complement
  let A : Subgroup G := MulAut.conj y • hyp.W2
  have hAcompl : A ≤ data.frobenius.complement.map data.L.subtype := by
    simpa only [A] using hyA
  have hAL : A ≤ data.L := hAcompl.trans (Subgroup.map_subtype_le _)
  have hAH : A ⊓ data.H = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, hxH⟩
    rw [Subgroup.mem_bot]
    let xL : ↥data.L := ⟨x, hAL hxA⟩
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp (hAcompl hxA)
    have hzxL : z = xL := Subtype.ext hzx
    have hxcompl : xL ∈ data.frobenius.complement := hzxL ▸ hz
    have hxkernel : xL ∈ data.frobenius.typeI.typeF.H.subgroupOf data.L := by
      rw [Subgroup.mem_subgroupOf, hkernel]
      exact hxH
    exact congrArg Subtype.val
      (Subgroup.disjoint_def.mp data.frobenius.frobenius.isComplement.disjoint
        hxkernel hxcompl)
  have hAcard : Nat.card ↥A = hyp.p := by
    change Nat.card ↥(MulAut.conj y • hyp.W2 : Subgroup G) = hyp.p
    rw [card_pointwise_smul, ← hyp.p_eq_card_W2]
  have hHnilp : Group.IsNilpotent ↥data.H := by
    rw [data.H_eq_LF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent data.L
  have hRnormal : (R : Subgroup ↥data.H).Normal :=
    OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent R
  have hRchar : (R : Subgroup ↥data.H).Characteristic :=
    Sylow.characteristic_of_normal R hRnormal
  have hARg : A ≤ Subgroup.normalizer (Rg : Set G) := by
    intro a ha
    have haL : a ∈ data.L := hAL ha
    have haNormH : a ∈ Subgroup.normalizer (data.H : Set G) := by
      have h := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer data.L haL
      rwa [← data.H_eq_LF] at h
    simpa only [Rg] using
      (OddOrder.BG.Ch1.S03f.mem_normalizer_map_subtype_of_characteristic
        (W := data.H) (C := (R : Subgroup ↥data.H)) haNormH)
  exact prime_dvd_sq_sub_one_of_frobenius_omega1Center
    hyp.p_prime hr hHL hFrobL (Subgroup.map_subtype_le _) hcard
    hAL hAH hAcard hARg

end OddOrder.Peterfalvi.S15

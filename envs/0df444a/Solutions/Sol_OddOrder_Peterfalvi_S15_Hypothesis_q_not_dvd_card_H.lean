-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.Hypothesis.q_not_dvd_card_H
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T15:53:00.135415+00:00
-- url     : https://prove2.me/submissions/8cf21005-b72c-45a9-8319-f01d7aa1975e

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_CountingLayer

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

section CountingLayer

open OddOrder.GroupTheory

/-- **`q ∤ |H|`** — the order-theoretic core of the `(H^#)^G ∩ (Q^#)^G = ∅` disjointness:
`H = PC ≤ S' = PU` has order dividing `|P|·|U|` (`derived_complement`), `q ∤ |P| = p^q`
(`p ≠ q`), and `q ∤ |U|` (the `U W₁` Frobenius structure has coprime kernel and complement,
`|W₁| = q`). -/
theorem _root_.solution [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : ¬ hyp.q ∣ Nat.card ↥hyp.H := by
  intro hdvd
  -- `|H| ∣ |S'| = |P|·|U|`.
  have hHle : hyp.H ≤ derivedInG hyp.S := by
    change hyp.P ⊔ hyp.C ≤ derivedInG hyp.S
    rw [hyp.S_deriv_eq_PU]
    exact sup_le le_sup_left (le_trans (hyp.C_eq ▸ inf_le_left) le_sup_right)
  have hcard_deriv : Nat.card ↥hyp.P * Nat.card ↥hyp.U = Nat.card ↥(derivedInG hyp.S) := by
    have h := hyp.Sdata.derived_complement.card_mul_card
    have hPeq : hyp.Sdata.H = hyp.P := by rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hPeq ▸ hyp.Sdata.H_le)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Sdata.U_le).toEquiv, hPeq,
      hyp.Sdata_U_eq] at h
  have hdvd' : hyp.q ∣ Nat.card ↥hyp.P * Nat.card ↥hyp.U := by
    rw [hcard_deriv]
    exact hdvd.trans (Subgroup.card_dvd_of_le hHle)
  rcases (Nat.Prime.dvd_mul hyp.q_prime).mp hdvd' with hq | hq
  · -- `q ∤ |P| = p^q` since `p ≠ q`.
    rw [hyp.card_P_eq hG hyp.Sdata_W2_eq] at hq
    have hqp : hyp.q ∣ hyp.p := Nat.Prime.dvd_of_dvd_pow hyp.q_prime hq
    exact hyp.p_ne_q ((Nat.prime_dvd_prime_iff_eq hyp.q_prime hyp.p_prime).mp hqp).symm
  · -- `q ∤ |U|`: `U W₁` Frobenius has coprime kernel/complement.
    -- `U ≠ ⊥` via the type-II/type-III common core (as in `basic_structure`).
    let setup := hyp.toTypesIIIIIIVSetupS hG
    have hSdataUne := setup.nontrivial.1
    change hyp.Sdata.U ≠ ⊥ at hSdataUne
    have hfrob := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius hyp.Sdata hSdataUne
    have hcop := hfrob.coprime_card_kernel_complement
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left :
        hyp.Sdata.U ≤ hyp.Sdata.U ⊔ hyp.Sdata.W1)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right :
        hyp.Sdata.W1 ≤ hyp.Sdata.U ⊔ hyp.Sdata.W1)).toEquiv,
      hyp.Sdata_U_eq, hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1] at hcop
    exact hyp.q_prime.ne_one (Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd hq dvd_rfl))

end CountingLayer

end OddOrder.Peterfalvi.S15

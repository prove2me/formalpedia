-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.Q_W2_structure
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:09:34.80987+00:00
-- url     : https://prove2.me/submissions/477f9562-6bea-4a42-89ac-886db86004d3

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_Gate3.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

-- ===== OddOrder/Peterfalvi/S15_Gate3.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.17.a) T-side Fitting order (B1)**: `|Q| = |T_F| = q^p`.

This is the `S ↔ T` symmetric companion of `BasicStructureData.P_order` (`|P| = |S_F| = p^q`), now
**proven** for the (14.9) type-II member `T`: from `IsTypeII T`, the (9.3) Wielandt order relation
`typeII_III_IV_order_relations` on the reconciled type-`P` data of `T` (`reconciled_typePData_T`)
gives `|T_F| = |tpd.W2|^|tpd.W1| = |W₁|^|W₂| = q^p` (the intrinsic factors reconcile to
`tpd.W2 = W₁`,
`tpd.W1 = W₂`).  Combined with the automorphism-equivariance of `M_F`
(`maxNilpotentNormalHall_pointwise_smul`), it gives `|L_F| = q^p` for every `L` conjugate to `T`,
which is what the `L ~ T` exclusion of (13.17.a) uses.  The `IsTypeII T` hypothesis is threaded from
`exists_LHypothesis` (§16, via the (14.9) `T_typeII`). -/
theorem card_Q_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) :
    Nat.card ↥hyp.Q = hyp.q ^ hyp.p := by
  obtain ⟨tpd, _htpdV, htpdW1, htpdW2⟩ := reconciled_typePData_T hG hyp
  have tdata : TypeIIData hyp.T := hTTypeII.some
  have hUne : tpd.U ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥tpd.U = Nat.card ↥tdata.typeP.U := by
      rw [tpd.card_U_eq_index, tdata.typeP.card_U_eq_index]
    rw [hbot, Subgroup.card_bot] at h1
    exact tdata.common.1 (Subgroup.card_eq_one.mp h1.symm)
  have hW1prime : (Nat.card ↥tpd.W1).Prime := by
    rw [htpdW1, ← hyp.p_eq_card_W2]; exact hyp.p_prime
  have hTI := tdata.common.2.2
  have hord := (OddOrder.Peterfalvi.S11.typeII_III_IV_order_relations hG
    { maximal := hyp.T_maximal
      typeP := tpd
      nontrivial := ⟨hUne, hW1prime, hTI⟩
      type_alt := Or.inl hTTypeII }).1 hTTypeII
  have hord2 : Nat.card ↥tpd.H = Nat.card ↥tpd.W2 ^ Nat.card ↥tpd.W1 := hord.2
  have hW2card : Nat.card ↥tpd.W2 = hyp.q := by
    rw [htpdW2, ← hyp.q_eq_card_W1]
  rw [tpd.H_eq, ← hyp.Q_eq_TF, hW2card, htpdW1, ← hyp.p_eq_card_W2] at hord2
  exact hord2

/-- §13 structural data for the semidirect product `Q ⋊ W₂` (`Q = T_F`) consumed by the
`∃ y` step of (13.17.c).  `W₂` normalizes `Q` (as `W₂ ≤ T` and `Q ◁ T`), meets it trivially, and
`p ∤ |Q| = q^p` (since `p ≠ q`).

*Proof.*  `W₂ ≤ W = S ⊓ T ≤ T` and `Q = T_F ◁ T` (`maxNilpotentNormalHall_le_normalizer`) give the
normalization.  The distinctness `p ≠ q` is forced because otherwise `W₁` and `W₂` would be equal
order-`q` subgroups of the cyclic `W` (`eq_of_card_eq_prime_of_isCyclic`), contradicting
`W₁ ⊓ W₂ = 1`; then `p ∤ q^p`, and the coprimality `|Q| ⟂ |W₂| = p` gives `Q ⊓ W₂ = 1`.  The only
gated input is `|Q| = q^p` (`card_Q_eq`, the isolated §13 counting residual B1). -/
theorem _root_.solution [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) :
    hyp.W2 ≤ Subgroup.normalizer (hyp.Q : Set G) ∧ hyp.Q ⊓ hyp.W2 = ⊥ ∧
      ¬ hyp.p ∣ Nat.card ↥hyp.Q := by
  -- `W₂ ≤ W = S ⊓ T ≤ T`.
  have hW2T : hyp.W2 ≤ hyp.T :=
    (le_sup_right.trans hyp.W_eq_join.ge).trans (hyp.W_eq_inter.le.trans inf_le_right)
  -- Conjunct 1: `W₂ ≤ N_G(Q)`, as `Q = T_F ◁ T` and `W₂ ≤ T`.
  have hWnorm : hyp.W2 ≤ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hyp.Q_eq_TF]
    exact hW2T.trans (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T)
  -- `p ≠ q`: else `W₁` and `W₂` are equal order-`q` subgroups of the cyclic `W`.
  have hpq : hyp.p ≠ hyp.q := by
    intro heq
    have : IsCyclic ↥hyp.W := hyp.W_cyclic
    have hW1W : hyp.W1 ≤ hyp.W := le_sup_left.trans hyp.W_eq_join.ge
    have hW2W : hyp.W2 ≤ hyp.W := le_sup_right.trans hyp.W_eq_join.ge
    have hW1card : Nat.card ↥(hyp.W1.subgroupOf hyp.W) = hyp.q := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1W).toEquiv]; exact hyp.q_eq_card_W1.symm
    have hW2card : Nat.card ↥(hyp.W2.subgroupOf hyp.W) = hyp.q := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2W).toEquiv, ← heq]
      exact hyp.p_eq_card_W2.symm
    have hsubeq : hyp.W1.subgroupOf hyp.W = hyp.W2.subgroupOf hyp.W :=
      Ch06.eq_of_card_eq_prime_of_isCyclic hyp.q_prime hW1card hW2card
    have hWeq : hyp.W1 = hyp.W2 := by
      have hmap := congrArg (Subgroup.map hyp.W.subtype) hsubeq
      rwa [Subgroup.map_subgroupOf_eq_of_le hW1W, Subgroup.map_subgroupOf_eq_of_le hW2W] at hmap
    have hbot : hyp.W1 = ⊥ := by
      have h := hyp.W1_inf_W2_eq_bot; rwa [← hWeq, inf_idem] at h
    have hq1 : hyp.q = 1 := by rw [hyp.q_eq_card_W1, hbot, Subgroup.card_bot]
    exact hyp.q_prime.one_lt.ne' hq1
  -- Conjunct 3: `p ∤ |Q| = q^p`, since `p ∤ q` (distinct primes).
  have hpQ : ¬ hyp.p ∣ Nat.card ↥hyp.Q := by
    rw [card_Q_eq hG hyp hTTypeII]
    intro hdvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hyp.p_prime hyp.q_prime).mp
      (hyp.p_prime.dvd_of_dvd_pow hdvd))
  -- Conjunct 2: `Q ⊓ W₂ = ⊥`, from coprimality `|Q| ⟂ p = |W₂|`.
  refine ⟨hWnorm, ?_, hpQ⟩
  apply Disjoint.eq_bot
  apply Subgroup.disjoint_of_coprime_natCard
  rw [← hyp.p_eq_card_W2]
  exact (hyp.p_prime.coprime_iff_not_dvd.mpr hpQ).symm

end OddOrder.Peterfalvi.S15

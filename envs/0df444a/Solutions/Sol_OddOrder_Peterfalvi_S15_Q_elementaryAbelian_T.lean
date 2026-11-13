-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.Q_elementaryAbelian_T
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:09:59.94956+00:00
-- url     : https://prove2.me/submissions/72d97c46-ba87-4905-90e8-6e5ddbd0d6b1

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

/-- **Peterfalvi (14.2.a), `T`-side dual of `BasicStructureGated.P_elementaryAbelian`**: the Fitting
kernel `Q = T_F` is elementary abelian of exponent `q`.

On the `S`-side this is the `§16`-carrier fact `P_elementaryAbelian` (from the type-`P₂` structure
of
`S`); `T` is likewise type-`P₂` (`IsTypeII T ↔ IsTypeP2 T`, `proposition_type_classification`), so
the
same σ-structure fact holds — `T_σ = T_F` is the elementary-abelian `q`-group of rank `p` on which
the
prime-order `κ`-factor `W₂` acts.  Proven as the exact dual of the `S`-side `P_elementaryAbelian`
(`S15_SAndT_Setup`, now sorry-free): the (14.9) type-II `T` gives a `TypesIIIIIIVSetup T` from the
reconciled `TypePData T` (`reconciled_typePData_T`) whose chief kernel `N = ⊥` (since `|Q| = q^p`,
`card_Q_eq`), so `Q` itself is the chief factor and carries `quotient_elementaryAbelian` at
`chief.p = q`.  Gated on the (14.9) `T_typeII` (through `card_Q_eq` / `reconciled_typePData_T`);
supplies the `hQ_elemAb` input of `normalizer_V_inf_W1_eq_bot_of_data`. -/
theorem _root_.solution [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) :
    IsElementaryAbelian hyp.q ↥hyp.Q := by
  classical
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
  let setupT : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup hyp.T :=
    { maximal := hyp.T_maximal
      typeP := tpd
      nontrivial := ⟨hUne, hW1prime, tdata.common.2.2⟩
      type_alt := Or.inl hTTypeII }
  obtain ⟨chief, _⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData hG setupT
  have := chief.N_normal
  have hHeq : (setupT.H : Subgroup G) = hyp.Q := by
    change tpd.H = hyp.Q; rw [tpd.H_eq, hyp.Q_eq_TF]
  have hqdim : setupT.q = hyp.p := by
    change Nat.card ↥tpd.W1 = hyp.p; rw [htpdW1, ← hyp.p_eq_card_W2]
  have hcardH : Nat.card ↥setupT.H = hyp.q ^ hyp.p := by
    -- Wielandt (9.3) order relation `|H| = |W₂|^|W₁|` for the type-II `T` (as in `card_Q_eq`,
    -- inlined since `card_Q_eq` is downstream of this lemma).
    have hord := (OddOrder.Peterfalvi.S11.typeII_III_IV_order_relations hG setupT).1 hTTypeII
    have hord2 : Nat.card ↥tpd.H = Nat.card ↥tpd.W2 ^ Nat.card ↥tpd.W1 := hord.2
    have hW2card : Nat.card ↥tpd.W2 = hyp.q := by rw [htpdW2, ← hyp.q_eq_card_W1]
    rw [hW2card, htpdW1, ← hyp.p_eq_card_W2] at hord2
    exact hord2
  have hquot := OddOrder.Peterfalvi.S11.chiefFactor_quotient_card chief
  rw [hqdim] at hquot
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup chief.N
  rw [hquot, hcardH] at hsplit
  -- `q^p = chief.p^p · |N|` forces `chief.p = q` and `|N| = 1`.
  have hdvd : chief.p ∣ hyp.q ^ hyp.p := by
    refine dvd_trans (dvd_pow_self chief.p hyp.p_prime.pos.ne') ?_
    exact hsplit ▸ Dvd.intro _ rfl
  have hpp : chief.p = hyp.q :=
    (Nat.prime_dvd_prime_iff_eq chief.p_prime hyp.q_prime).mp
      (chief.p_prime.dvd_of_dvd_pow hdvd)
  rw [hpp] at hsplit
  have hN : chief.N = ⊥ := by
    have hN1 : Nat.card ↥chief.N = 1 := by
      have := hsplit.symm
      nlinarith [Nat.card_pos (α := ↥chief.N), pow_pos hyp.q_prime.pos hyp.p]
    exact Subgroup.card_eq_one.mp hN1
  have hEA : IsElementaryAbelian hyp.q ↥setupT.H := by
    have h := chief.quotient_elementaryAbelian
    rw [hpp] at h
    exact OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hN).trans QuotientGroup.quotientBot) h
  rwa [hHeq] at hEA

end OddOrder.Peterfalvi.S15

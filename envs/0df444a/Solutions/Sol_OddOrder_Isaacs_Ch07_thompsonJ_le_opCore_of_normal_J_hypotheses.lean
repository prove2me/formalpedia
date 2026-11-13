-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.thompsonJ_le_opCore_of_normal_J_hypotheses
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T06:03:44.542922+00:00
-- url     : https://prove2.me/submissions/b9b0ae85-e076-44c9-ad69-1c410f26c469

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ_Setup.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJClose.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B1_NormalJ_Setup
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJClose
import Theorems.Thm_OddOrder_Isaacs_Ch07_normal_thompsonJ_of_le_opCore
import Theorems.Thm_OddOrder_Isaacs_Ch07_centralizer_omega1ZCenterOpCore_isPGroup
import Theorems.Thm_OddOrder_Isaacs_Ch07_omega1ZCenterOpCore_relIndex_inter_A_le
import Theorems.Thm_OddOrder_Isaacs_Ch07_step8a_PBar_normal_GBar
import Theorems.Thm_OddOrder_Isaacs_Ch07_step4_5_normal_J_hypotheses

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ_Setup.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Step 2 entry / Step 7 closure**: `J(P) ≤ X` iff every elementary abelian
maximal `E ∈ E(P)` is contained in `X`.  Pure unfold of the iSup definition. -/
theorem thompsonJ_le_iff
    {G : Type*} [Group G] (P X : Subgroup G) (p : ℕ) :
    Subgroup.thompsonJ P p ≤ X ↔
      ∀ E ∈ Subgroup.maxElemAbelianIn P p, E ≤ X := by
  unfold Subgroup.thompsonJ
  exact iSup₂_le_iff

/-- **Isaacs Thm 7.6 Step 6 conclusion** (mmd L3882): if `K = C_G(V)` is a
`p`-group, then `K ≤ O_p(G)` via `normal_pgroup_le_opCore`. -/
theorem centralizer_omega1ZCenterOpCore_le_opCore_of_isPGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hK_pg : IsPGroup p (Subgroup.centralizer (omega1ZCenterOpCore G p : Set G))) :
    Subgroup.centralizer (omega1ZCenterOpCore G p : Set G) ≤
      OddOrder.Isaacs.Ch01.opCore p G :=
  OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hK_pg

end OddOrder.Isaacs.Ch07

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Isaacs Thm 7.6 Step 6 faithfulness** (mmd L3884): `K̄ = ⊥` in `Ḡ` given
`K ≤ U`.  This is the final Step 6 conclusion: the Ḡ-action on V is faithful
because its kernel `K̄ = (K.map mk')` is trivial. -/
theorem centralizer_omega1ZCenterOpCore_map_eq_bot_of_le_opCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hK_le_U : Subgroup.centralizer (omega1ZCenterOpCore G p : Set G) ≤
        OddOrder.Isaacs.Ch01.opCore p G) :
    (Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)).map
        (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) = ⊥ := by
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  -- Goal: K ≤ oPiCore {p} G
  intro x hx
  have hx_U : x ∈ OddOrder.Isaacs.Ch01.opCore p G := hK_le_U hx
  rwa [show OddOrder.Isaacs.Ch01.opCore p G =
        OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G from
      (OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p).symm] at hx_U

end OddOrder.Isaacs.Ch07

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJClose.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Isaacs Thm 7.6 Step 8b** (mmd L3896): pull back `P̄ ⊴ Ḡ` to derive `False`.

Once `P̄ ⊴ Ḡ` is established (Step 8a), correspondence-theorem reasoning gives
`P ⊴ G` (since `U ≤ P`, the preimage of `P̄` is `P`).  Then `P.Normal` and
`IsPGroup p P` give `P ≤ opCore p G = U` via `normal_pgroup_le_opCore`.
Combined with `A ≤ P`, this contradicts `A ⊄ U`. -/
theorem step8b_pullback_normal_P
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    {A : Subgroup G}
    (hA_le_P : A ≤ (P : Subgroup G))
    (hA_not_le : ¬ A ≤ OddOrder.Isaacs.Ch01.opCore p G)
    (hPBar_normal :
       ((P : Subgroup G).map
         (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))).Normal) :
    False := by
  -- (1) U ≤ P (general).
  have hU_le_P : OddOrder.Isaacs.Ch01.opCore p G ≤ (P : Subgroup G) :=
    OddOrder.Isaacs.Ch01.opCore_le P
  -- (2) U ≤ oPiCore_p (definitionally equal).
  have hU_eq : OddOrder.Isaacs.Ch01.opCore p G =
      OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    (OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p).symm
  -- (3) (P.map mk').comap mk' = P (since U ≤ P, and U = kernel of mk').
  have hP_preimage :
      ((P : Subgroup G).map
        (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))).comap
          (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) =
        (P : Subgroup G) := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    -- Goal: P ⊔ oPiCore {p} G = P. Use U ≤ P.
    rw [← hU_eq]
    exact sup_eq_left.mpr hU_le_P
  -- (4) P̄ ⊴ Ḡ ⇒ comap P̄ = P is normal in G.
  have hP_normal : (P : Subgroup G).Normal := by
    rw [← hP_preimage]
    exact hPBar_normal.comap (QuotientGroup.mk' _)
  -- (5) P is a normal p-group ⇒ P ≤ opCore p G = U.
  have hP_pg : IsPGroup p (P : Subgroup G) := P.isPGroup'
  have := hP_normal
  have hP_le_U : (P : Subgroup G) ≤ OddOrder.Isaacs.Ch01.opCore p G :=
    OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hP_pg
  -- (6) A ≤ P ≤ U contradicts hA_not_le.
  exact hA_not_le (hA_le_P.trans hP_le_U)

/-- **Isaacs Thm 7.6 Step 1-7 conclusion**: `J(P) ≤ O_p(G)`.

Proved by strong induction on `Nat.card G` (so Step 3 can use the IH on proper
subgroups) + Step 2 extraction (`thompsonJ_le_iff`) + Steps 4-5
(`step4_5_normal_J_hypotheses`, proved) + Step 6 (`...isPGroup` /
`...le_opCore_of_isPGroup` / `...map_eq_bot_of_le_opCore`) + Step 7
(`omega1ZCenterOpCore_relIndex_inter_A_le`) + Step 8
(`step8a_PBar_normal_GBar` / `step8b_pullback_normal_P`).  All steps are
proved theorems (nothing is axiomatized); Ch07 is sorry-free. -/
theorem _root_.solution
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp2 : p ≠ 2)
    (h_pSolvable : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G)) :
    Subgroup.thompsonJ (P : Subgroup G) p ≤ OddOrder.Isaacs.Ch01.opCore p G := by
  classical
  -- Strong induction on `Nat.card G`, with the motive parametrized over arbitrary
  -- groups whose order is less than `|G|` and which satisfy the descended hypotheses.
  let motive : ℕ → Prop := fun n =>
    ∀ (H : Type _) [Group H] [Finite H] [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) H]
      (_h2abelian : ∀ S : Subgroup H, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
      (_h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} H = ⊥)
      (Q : Sylow p H)
      (_h_centralizer_center :
         Subgroup.centralizer
           (((Subgroup.center (Q : Subgroup H)).map (Q : Subgroup H).subtype) : Set H)
           = (Q : Subgroup H)),
      Nat.card H = n → Subgroup.thompsonJ (Q : Subgroup H) p ≤ OddOrder.Isaacs.Ch01.opCore p H
  suffices hmain : motive (Nat.card G) by
    exact hmain G h2abelian h_oPiPrime_trivial P h_centralizer_center rfl
  refine Nat.strong_induction_on (Nat.card G) ?_
  intro n ih H _ _ _ h2abelian' h_oPiPrime_trivial' Q h_centralizer_center' hcard
  -- The induction hypothesis at the "normal_J" level (i.e., normality of J(Q')
  -- in H' for groups H' with order < n).
  have ih_normal :
      ∀ (H' : Type _) [Group H'] [Finite H']
        [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) H'],
      Nat.card H' < Nat.card H →
      (∀ S : Subgroup H', IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x) →
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} H' = ⊥ →
      ∀ (Q' : Sylow p H'),
        Subgroup.centralizer
            (((Subgroup.center (Q' : Subgroup H')).map
              (Q' : Subgroup H').subtype) : Set H')
          = (Q' : Subgroup H') →
        (Subgroup.thompsonJ (Q' : Subgroup H') p).Normal := by
    intro H' _ _ _ hH'_lt h2abelian'' h_oPiPrime_trivial'' Q' h_centralizer_center''
    have hH'_lt_n : Nat.card H' < n := hH'_lt.trans_eq hcard
    have h_le_op' :=
      ih (Nat.card H') hH'_lt_n H' h2abelian'' h_oPiPrime_trivial'' Q' h_centralizer_center'' rfl
    exact normal_thompsonJ_of_le_opCore Q' h_le_op'
  -- Now prove `J(Q) ≤ U` on the running group `H` of order `n` using Step 2 extraction
  -- + the Steps 4-5 lemma + Step 6 (landed) + Step 7 (landed) + Step 8 closure lemma.
  have h_pSolvable_in_H : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) H :=
    inferInstance
  rw [thompsonJ_le_iff]
  intro A hA_mem
  by_contra hA_not_le
  -- Package the induction hypothesis for use by the Step 4-5 lemma.
  have ih_for_axioms :
      ∀ (H' : Type _) [Group H'] [Finite H']
        [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) H'],
      Nat.card H' < Nat.card H →
      (∀ S : Subgroup H', IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x) →
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} H' = ⊥ →
      ∀ (Q' : Sylow p H'),
        Subgroup.centralizer
            (((Subgroup.center (Q' : Subgroup H')).map
              (Q' : Subgroup H').subtype) : Set H')
          = (Q' : Subgroup H') →
        (Subgroup.thompsonJ (Q' : Subgroup H') p).Normal :=
    fun H' _ _ _ hH'_lt h2 h_oPi Q' h_cent =>
      ih_normal H' hH'_lt h2 h_oPi Q' h_cent
  -- (Step 4 + Step 5): `P = UA` and `A.relIndex U = p` (= `|Ā| = p`).
  obtain ⟨h_P_eq_UA, h_Abar_card_eq_p⟩ :=
    step4_5_normal_J_hypotheses (G := H) Q hp2 h_pSolvable_in_H h2abelian'
      h_oPiPrime_trivial' h_centralizer_center' ih_for_axioms hA_mem hA_not_le
  have hA_D_relIndex : (OddOrder.Isaacs.Ch01.opCore p H).relIndex A ≤ p :=
    le_of_eq h_Abar_card_eq_p
  -- (Step 7): `A.relIndex V ≤ p`, from the landed counting lemma.
  have hV_inter_A_le_p : A.relIndex (omega1ZCenterOpCore H p) ≤ p :=
    omega1ZCenterOpCore_relIndex_inter_A_le Q hA_mem hA_D_relIndex
  -- (Step 6): `K̄ = ⊥` from K = C_G(V) being a p-group (landed), hence K ≤ U.
  have h_K_pg : IsPGroup p (Subgroup.centralizer (omega1ZCenterOpCore H p : Set H)) :=
    centralizer_omega1ZCenterOpCore_isPGroup h_oPiPrime_trivial' Q h_centralizer_center'
  have h_K_le_U : Subgroup.centralizer (omega1ZCenterOpCore H p : Set H) ≤
      OddOrder.Isaacs.Ch01.opCore p H :=
    centralizer_omega1ZCenterOpCore_le_opCore_of_isPGroup h_K_pg
  have h_K_map_eq_bot :
      (Subgroup.centralizer (omega1ZCenterOpCore H p : Set H)).map
        (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) H)) = ⊥ :=
    centralizer_omega1ZCenterOpCore_map_eq_bot_of_le_opCore h_K_le_U
  -- (Step 8a): apply Thm 7.5 to get P̄ ⊴ Ḡ.
  have hPBar_normal :
      ((Q : Subgroup H).map (QuotientGroup.mk'
        (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) H))).Normal :=
    step8a_PBar_normal_GBar (G := H) Q hp2 h_pSolvable_in_H h2abelian'
      h_oPiPrime_trivial' h_centralizer_center' hA_mem h_P_eq_UA h_Abar_card_eq_p
      hV_inter_A_le_p h_K_map_eq_bot
  -- (Step 8b): pull back P̄ ⊴ Ḡ to derive `False` from `A ⊆ P ⊆ U`.
  exact step8b_pullback_normal_P Q hA_mem.1 hA_not_le hPBar_normal

end OddOrder.Isaacs.Ch07

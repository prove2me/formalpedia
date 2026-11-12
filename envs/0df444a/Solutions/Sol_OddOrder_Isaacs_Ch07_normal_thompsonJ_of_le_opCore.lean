-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.normal_thompsonJ_of_le_opCore
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:50:34.737223+00:00
-- url     : https://prove2.me/submissions/98a92d21-5f32-4737-9626-bf51626a7f5d

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/ThompsonSubgroup.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B1_NormalJ_Setup
import Definitions.Def_OddOrder_GroupTheory_ThompsonSubgroup
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas

-- ===== OddOrder/GroupTheory/ThompsonSubgroup.lean =====
namespace Subgroup

variable {G : Type*} [Group G]

/-- The trivial subgroup `⊥` is `p`-elementary abelian for any `p`. -/
theorem bot_isElementaryAbelian (p : ℕ) :
    (⊥ : Subgroup G).IsElementaryAbelian p := by
  refine ⟨?_, ?_⟩
  · intro x y
    exact Subsingleton.elim _ _
  · intro x
    have hx : x = 1 := Subsingleton.elim x 1
    rw [hx, one_pow]

/-- `[Finite G]` のもとで `maxElemAbelianIn P p` は非空 (`⊥` が常に元). -/
theorem maxElemAbelianIn_nonempty [Finite G] (P : Subgroup G) (p : ℕ) :
    (maxElemAbelianIn P p).Nonempty := by
  -- S = {F ≤ P | F elem ab} は有限・非空 (⊥ ∈ S).
  have hUniv : (Set.univ : Set (Subgroup G)).Finite := Set.finite_univ
  have hS_fin : {F : Subgroup G | F ≤ P ∧ F.IsElementaryAbelian p}.Finite :=
    hUniv.subset (fun _ _ => Set.mem_univ _)
  have hS_ne : {F : Subgroup G | F ≤ P ∧ F.IsElementaryAbelian p}.Nonempty :=
    ⟨⊥, bot_le, bot_isElementaryAbelian p⟩
  -- 最大位数の元 E を取得.
  obtain ⟨E, hE_S, hE_max⟩ :=
    Set.exists_max_image
      {F : Subgroup G | F ≤ P ∧ F.IsElementaryAbelian p}
      (fun F => Nat.card F) hS_fin hS_ne
  refine ⟨E, hE_S.1, hE_S.2, ?_⟩
  intro F hF_P hF_el
  exact hE_max F ⟨hF_P, hF_el⟩

/-- **Isaacs Thm 7.2** (J(P) は Q 内でも変わらない).

`J(P) ≤ Q ≤ P` のとき `J(Q) = J(P)`. 系として **`J(P)` は `Q` 内 characteristic**
(`J(Q)` は Q 内 characteristic で自動的に従う性質, 別途).

証明: `maxElemAbelianIn Q p = maxElemAbelianIn P p` を示す.
- `Q ⊆ P` 側: `E ∈ maxElemAbelianIn P p` ⇒ `E ≤ J(P) ≤ Q`, `Q` 内でも max (任意の
  `F ≤ Q ≤ P` elem ab で `|F| ≤ |E|`).
- `P ⊆ Q` 側: `E₀ ∈ maxElemAbelianIn P p` を fix し `E₀ ≤ Q`. `E ∈ maxElemAbelianIn Q p`
  なら `|E₀| ≤ |E|` (E max in Q) かつ `|E| ≤ |E₀|` (E ≤ P, E₀ max in P) で位数一致.
  位数一致から `E` も `P` 内 max. -/
theorem thompsonJ_eq_of_le_of_le [Finite G] {P Q : Subgroup G} {p : ℕ}
    (hJQ : thompsonJ P p ≤ Q) (hQP : Q ≤ P) :
    thompsonJ Q p = thompsonJ P p := by
  apply le_antisymm
  · -- J(Q) ≤ J(P)
    refine iSup_le fun E => iSup_le fun hE_Q => ?_
    -- E max in Q.  E ∈ maxElemAbelianIn P p を示す.
    obtain ⟨E₀, hE₀_P, hE₀_el, hE₀_max⟩ := maxElemAbelianIn_nonempty P p
    have hE₀_le_J : E₀ ≤ thompsonJ P p :=
      le_thompsonJ_of_mem_maxElemAbelianIn ⟨hE₀_P, hE₀_el, hE₀_max⟩
    have hE₀_Q : E₀ ≤ Q := hE₀_le_J.trans hJQ
    have hcard_E₀_le_E : Nat.card E₀ ≤ Nat.card E := hE_Q.2.2 E₀ hE₀_Q hE₀_el
    have hE_P : E ≤ P := hE_Q.1.trans hQP
    have hcard_E_le_E₀ : Nat.card E ≤ Nat.card E₀ := hE₀_max E hE_P hE_Q.2.1
    have hcard_eq : Nat.card E = Nat.card E₀ := le_antisymm hcard_E_le_E₀ hcard_E₀_le_E
    apply le_thompsonJ_of_mem_maxElemAbelianIn
    refine ⟨hE_P, hE_Q.2.1, ?_⟩
    intro F hF_P hF_el
    calc Nat.card F
        ≤ Nat.card E₀ := hE₀_max F hF_P hF_el
      _ = Nat.card E := hcard_eq.symm
  · -- J(P) ≤ J(Q)
    refine iSup_le fun E => iSup_le fun hE_P => ?_
    have hE_le_J : E ≤ thompsonJ P p :=
      le_thompsonJ_of_mem_maxElemAbelianIn hE_P
    have hE_Q : E ≤ Q := hE_le_J.trans hJQ
    apply le_thompsonJ_of_mem_maxElemAbelianIn
    refine ⟨hE_Q, hE_P.2.1, ?_⟩
    intro F hF_Q hF_el
    exact hE_P.2.2 F (hF_Q.trans hQP) hF_el

end Subgroup

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Isaacs Thm 7.6 Step 8** (mmd L3893): if `J(P) ≤ L` and `L ≤ P` then
`J(L) = J(P)`, the consequence of Thm 7.2 needed in the closing step. -/
private theorem thompsonJ_opCore_eq_thompsonJ_sylow_of_thompsonJ_le_opCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} (P : Sylow p G)
    (h_le : Subgroup.thompsonJ (P : Subgroup G) p ≤ OddOrder.Isaacs.Ch01.opCore p G) :
    Subgroup.thompsonJ (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p =
      Subgroup.thompsonJ (P : Subgroup G) p :=
  Subgroup.thompsonJ_eq_of_le_of_le h_le (OddOrder.Isaacs.Ch01.opCore_le P)

/-- **Conjugating `maxElemAbelianIn L p` by `g ∈ G`** when `L` is `G`-normal.

If `L ⊴ G` and `E ∈ maxElemAbelianIn L p`, then for any `g : G`, the conjugate
`g E g⁻¹` is again in `maxElemAbelianIn L p`.  Pure normality + the fact that
conjugation is an isomorphism (preserves cardinality and elementary-abelian
property). -/
private theorem maxElemAbelianIn_conj_mem
    {G : Type*} [Group G] {L E : Subgroup G} [hL : L.Normal] {p : ℕ}
    (hE : E ∈ Subgroup.maxElemAbelianIn L p) (g : G) :
    E.map (MulAut.conj g).toMonoidHom ∈ Subgroup.maxElemAbelianIn L p := by
  refine ⟨?_, ?_, ?_⟩
  · -- E.map (conj g) ≤ L
    rintro _ ⟨e, he_E, rfl⟩
    have he_L : e ∈ L := hE.1 he_E
    change g * e * g⁻¹ ∈ L
    exact hL.conj_mem _ he_L g
  · -- E.map (conj g) is elementary abelian
    refine ⟨?_, ?_⟩
    · rintro ⟨_, ⟨a, ha_E, rfl⟩⟩ ⟨_, ⟨b, hb_E, rfl⟩⟩
      apply Subtype.ext
      change (g * a * g⁻¹) * (g * b * g⁻¹) = (g * b * g⁻¹) * (g * a * g⁻¹)
      have habcomm : a * b = b * a := by
        have h := hE.2.1.comm ⟨a, ha_E⟩ ⟨b, hb_E⟩
        exact congr_arg Subtype.val h
      calc (g * a * g⁻¹) * (g * b * g⁻¹)
          = g * (a * b) * g⁻¹ := by group
        _ = g * (b * a) * g⁻¹ := by rw [habcomm]
        _ = (g * b * g⁻¹) * (g * a * g⁻¹) := by group
    · rintro ⟨_, ⟨a, ha_E, rfl⟩⟩
      apply Subtype.ext
      change (g * a * g⁻¹) ^ p = 1
      have ha_p : a ^ p = 1 := by
        have h := hE.2.1.pow_eq_one ⟨a, ha_E⟩
        exact congr_arg Subtype.val h
      calc (g * a * g⁻¹) ^ p
          = g * a ^ p * g⁻¹ := by
            rw [conj_pow]
        _ = g * 1 * g⁻¹ := by rw [ha_p]
        _ = 1 := by group
  · -- E.map (conj g) is of maximum cardinality
    intro F hF_L hF_el
    have hF_conj_card : Nat.card (F.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) =
        Nat.card F :=
      Subgroup.card_map_of_injective (MulEquiv.injective _)
    have hE_conj_card : Nat.card (E.map (MulAut.conj g).toMonoidHom : Subgroup G) =
        Nat.card E :=
      Subgroup.card_map_of_injective (MulEquiv.injective _)
    rw [hE_conj_card]
    have hF_inv : F.map (MulAut.conj g⁻¹).toMonoidHom ≤ L := by
      rintro _ ⟨e, he_F, rfl⟩
      have he_L : e ∈ L := hF_L he_F
      change g⁻¹ * e * g⁻¹⁻¹ ∈ L
      exact hL.conj_mem _ he_L g⁻¹
    have hF_inv_el : (F.map (MulAut.conj g⁻¹).toMonoidHom).IsElementaryAbelian p := by
      refine ⟨?_, ?_⟩
      · rintro ⟨_, ⟨a, ha_F, rfl⟩⟩ ⟨_, ⟨b, hb_F, rfl⟩⟩
        apply Subtype.ext
        change (g⁻¹ * a * g⁻¹⁻¹) * (g⁻¹ * b * g⁻¹⁻¹) =
          (g⁻¹ * b * g⁻¹⁻¹) * (g⁻¹ * a * g⁻¹⁻¹)
        have habcomm : a * b = b * a := by
          have h := hF_el.comm ⟨a, ha_F⟩ ⟨b, hb_F⟩
          exact congr_arg Subtype.val h
        calc (g⁻¹ * a * g⁻¹⁻¹) * (g⁻¹ * b * g⁻¹⁻¹)
            = g⁻¹ * (a * b) * g⁻¹⁻¹ := by group
          _ = g⁻¹ * (b * a) * g⁻¹⁻¹ := by rw [habcomm]
          _ = (g⁻¹ * b * g⁻¹⁻¹) * (g⁻¹ * a * g⁻¹⁻¹) := by group
      · rintro ⟨_, ⟨a, ha_F, rfl⟩⟩
        apply Subtype.ext
        change (g⁻¹ * a * g⁻¹⁻¹) ^ p = 1
        have ha_p : a ^ p = 1 := by
          have h := hF_el.pow_eq_one ⟨a, ha_F⟩
          exact congr_arg Subtype.val h
        calc (g⁻¹ * a * g⁻¹⁻¹) ^ p
            = g⁻¹ * a ^ p * g⁻¹⁻¹ := by rw [conj_pow]
          _ = g⁻¹ * 1 * g⁻¹⁻¹ := by rw [ha_p]
          _ = 1 := by group
    have := hE.2.2 (F.map (MulAut.conj g⁻¹).toMonoidHom) hF_inv hF_inv_el
    rw [hF_conj_card] at this
    exact this

/-- **Isaacs Thm 7.6 Step 8** (mmd L3893-3896): under the running hypotheses, the
**conditional conclusion** of Step 2 (`J(P) ≤ L`) yields normality of `J(P)` in `G`.

Strategy: from `J(P) ≤ L = O_p(G)` and the Step 2 / Thm 7.2 bridge, `J(L) = J(P)`.
Then `g ∈ G`, `E ∈ E(L)` ⇒ `g E g⁻¹ ∈ E(L)` (`maxElemAbelianIn_conj_mem`), so the
iSup defining `J(L)` is `G`-stable. -/
theorem _root_.solution
    {G : Type*} [Group G] [Finite G] {p : ℕ} (P : Sylow p G)
    (h_le : Subgroup.thompsonJ (P : Subgroup G) p ≤ OddOrder.Isaacs.Ch01.opCore p G) :
    (Subgroup.thompsonJ (P : Subgroup G) p).Normal := by
  -- Replace J(P) by J(L) using Thm 7.2.
  have hJLP : Subgroup.thompsonJ (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p =
      Subgroup.thompsonJ (P : Subgroup G) p :=
    thompsonJ_opCore_eq_thompsonJ_sylow_of_thompsonJ_le_opCore P h_le
  rw [← hJLP]
  -- It suffices to show: ∀ g ∈ G, (J(L)).map (conj g) ≤ J(L).
  refine ⟨?_⟩
  intro n hn g
  -- Reduce to: g * J(L) * g⁻¹ ≤ J(L).
  -- We show `(J(L)).map (MulAut.conj g).toMonoidHom ≤ J(L)`.
  have h_map_le :
      (Subgroup.thompsonJ (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p).map
        (MulAut.conj g).toMonoidHom ≤
      Subgroup.thompsonJ (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p := by
    rw [show Subgroup.thompsonJ (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p
          = ⨆ E ∈ Subgroup.maxElemAbelianIn
            (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p, E from rfl,
        Subgroup.map_iSup]
    refine iSup_le fun E => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hE_mem => ?_
    -- E.map (conj g) ∈ maxElemAbelianIn L p, so E.map (conj g) ≤ J(L).
    have h_conj_mem :=
      maxElemAbelianIn_conj_mem (L := OddOrder.Isaacs.Ch01.opCore p G) hE_mem g
    exact Subgroup.le_thompsonJ_of_mem_maxElemAbelianIn h_conj_mem
  have : g * n * g⁻¹ ∈ (Subgroup.thompsonJ
      (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p).map
        (MulAut.conj g).toMonoidHom := by
    refine ⟨n, hn, ?_⟩
    change g * n * g⁻¹ = g * n * g⁻¹
    rfl
  exact h_map_le this

end OddOrder.Isaacs.Ch07

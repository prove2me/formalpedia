-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.exists_mem_conj_W2_le_of_dvd_card
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:07:47.316375+00:00
-- url     : https://prove2.me/submissions/626fd3b8-c9cb-43d2-964d-2f32ca79c105

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

/-- **Group-theoretic core of the `∃ y ∈ Q, W₂^y ≤ E` step of Peterfalvi (13.17.c).**

Let `Q ⊔ W₂` be a semidirect product `Q ⋊ W₂` with `Q` a (solvable) normal Hall subgroup
(`W₂ ≤ N(Q)`, `Q ⊓ W₂ = ⊥`, `|W₂| = p` prime, `p ∤ |Q|`).  Then any subgroup `E ≤ Q ⊔ W₂`
whose order is divisible by `p` contains a `Q`-conjugate of `W₂`.

*Proof:* an order-`p` subgroup `P ≤ E` (Cauchy) is coprime to the normal complemented `Q`, so by
Schur–Zassenhaus complement conjugacy (`exists_conj_le_of_isComplement'_of_coprime`, applied inside
`↥(Q ⊔ W₂)`) it lies in a conjugate `W₂^g` of the complement `W₂`; cardinalities force `P = W₂^g`.
Decomposing `g = q w` (`q ∈ Q`, `w ∈ W₂`) gives `W₂^g = W₂^q`, so `W₂^q = P ≤ E` with `q ∈ Q`. -/
theorem _root_.solution [Finite G]
    {Q W2 E : Subgroup G} (hWnorm : W2 ≤ Subgroup.normalizer (Q : Set G))
    (hQsolv : Group.IsSolvable ↥Q) (hdisj : Q ⊓ W2 = ⊥)
    {p : ℕ} (hp : p.Prime) (hW2 : Nat.card ↥W2 = p) (hpQ : ¬ p ∣ Nat.card ↥Q)
    (hE : E ≤ Q ⊔ W2) (hpE : p ∣ Nat.card ↥E) :
    ∃ y ∈ Q, (MulAut.conj y • W2 : Subgroup G) ≤ E := by
  have : Fact p.Prime := ⟨hp⟩
  set K : Subgroup G := Q ⊔ W2 with hKdef
  -- `Q` and `W₂`, transported into `↥K`, with `Q` normal and complementing `W₂`.
  have hQK : Q ≤ K := le_sup_left
  have hW2K : W2 ≤ K := le_sup_right
  have hQ'normal : (Q.subgroupOf K).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (by
      rw [hKdef]; exact sup_le Subgroup.le_normalizer hWnorm)
  have hsup_top : (Q.subgroupOf K) ⊔ (W2.subgroupOf K) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQK hW2K, ← hKdef, Subgroup.subgroupOf_self]
  have hcompl : (Q.subgroupOf K).IsComplement' (W2.subgroupOf K) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · rw [disjoint_iff, eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hy
      have hyQW : (y : G) ∈ Q ⊓ W2 := ⟨hy.1, hy.2⟩
      rw [hdisj, Subgroup.mem_bot] at hyQW
      rw [Subgroup.mem_bot]; exact Subtype.ext hyQW
    · rw [← Subgroup.normal_mul, hsup_top, Subgroup.coe_top]
  -- An order-`p` subgroup `P ≤ E` (Cauchy).
  have : Fintype ↥E := Fintype.ofFinite _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := ↥E) p (by
    rwa [Nat.card_eq_fintype_card] at hpE)
  set z : G := (x : G) with hzdef
  have hzE : z ∈ E := x.2
  have hzord : orderOf z = p := by
    have h : orderOf z = orderOf x := orderOf_injective E.subtype Subtype.coe_injective x
    rw [h]; exact hx
  set P : Subgroup G := Subgroup.zpowers z with hPdef
  have hPcard : Nat.card ↥P = p := by rw [hPdef, Nat.card_zpowers, hzord]
  have hPE : P ≤ E := (Subgroup.zpowers_le).mpr hzE
  have hPK : P ≤ K := hPE.trans hE
  -- `P` (inside `↥K`) is coprime to `Q`, so it lies in a conjugate of `W₂`.
  have hcop : Nat.Coprime (Nat.card ↥(P.subgroupOf K)) (Nat.card ↥(Q.subgroupOf K)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv, hPcard]
    exact (hp.coprime_iff_not_dvd).mpr hpQ
  have : Group.IsSolvable ↥Q := hQsolv
  have hQ'solv : Group.IsSolvable ↥(Q.subgroupOf K) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hQK).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hQK).symm.surjective
  obtain ⟨ξ, hξ⟩ := Ch03.exists_conj_le_of_isComplement'_of_coprime hQ'solv hcompl hcop
  -- Decompose `ξ = q' * w'` in `↥K` (`Q'` normal complement).
  have hξprod : (ξ : ↥K) ∈ (↑(Q.subgroupOf K) : Set ↥K) * (↑(W2.subgroupOf K) : Set ↥K) := by
    rw [← Subgroup.normal_mul, hsup_top, Subgroup.coe_top]; exact Set.mem_univ ξ
  obtain ⟨q', hq', w', hw', hqw⟩ := Set.mem_mul.mp hξprod
  refine ⟨(q' : G), (Subgroup.mem_subgroupOf.mp hq'), ?_⟩
  -- `W₂^(↑q') = W₂^ξ ⊇ P`, and cardinalities give equality.
  have hconj_le : P ≤ MulAut.conj (q' : G) • W2 := by
    intro a ha
    -- `a ∈ P`, so `⟨a,_⟩ ∈ P.subgroupOf K ≤ (W₂.subgroupOf K).map (conj ξ)`.
    have haK : a ∈ K := hPK ha
    have ha' : (⟨a, haK⟩ : ↥K) ∈ (W2.subgroupOf K).map (MulAut.conj ξ).toMonoidHom :=
      hξ (by rw [Subgroup.mem_subgroupOf]; exact ha)
    rw [Subgroup.mem_map] at ha'
    obtain ⟨v, hv, hva⟩ := ha'
    -- `v ∈ W₂'`, `conj ξ v = ⟨a,_⟩`; project to `G`: `ξ v ξ⁻¹ = a`.
    rw [Subgroup.mem_subgroupOf] at hv
    have hvW2 : (v : G) ∈ W2 := hv
    have hval : (ξ : G) * (v : G) * (ξ : G)⁻¹ = a := by
      have h := congrArg (Subgroup.subtype K) hva
      simpa [MulAut.conj_apply] using h
    -- `ξ = q' w'`.
    have hξqw : (ξ : G) = (q' : G) * (w' : G) := by
      have h := congrArg (Subgroup.subtype K) hqw
      simpa using h.symm
    have hw'W2 : (w' : G) ∈ W2 := hw'
    have hconj_w : (w' : G) * (v : G) * (w' : G)⁻¹ ∈ W2 :=
      W2.mul_mem (W2.mul_mem hw'W2 hvW2) (W2.inv_mem hw'W2)
    -- `a = q' (w' v w'⁻¹) q'⁻¹ ∈ W₂.map (conj q')`.
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply,
      ← hval, hξqw]
    have hsimp : (q' : G)⁻¹ * ((q' : G) * (w' : G) * (v : G) * ((q' : G) * (w' : G))⁻¹) * (q' : G)
        = (w' : G) * (v : G) * (w' : G)⁻¹ := by group
    rw [hsimp]; exact hconj_w
  -- `P = W₂^(↑q')` by cardinality, and `P ≤ E`.
  have hmap : (MulAut.conj (q' : G) • W2 : Subgroup G)
      = W2.map (MulAut.conj (q' : G)).toMonoidHom := by
    rw [Subgroup.pointwise_smul_def]; rfl
  have hcard_eq : Nat.card ↥(MulAut.conj (q' : G) • W2 : Subgroup G) = p := by
    rw [hmap, Nat.card_congr (Subgroup.equivMapOfInjective W2
      (MulAut.conj (q' : G)).toMonoidHom (MulAut.conj (q' : G)).injective).toEquiv.symm, hW2]
  have hPeq : P = MulAut.conj (q' : G) • W2 :=
    Subgroup.eq_of_le_of_card_ge hconj_le (by rw [hcard_eq, hPcard])
  rw [← hPeq]; exact hPE

end OddOrder.Peterfalvi.S15

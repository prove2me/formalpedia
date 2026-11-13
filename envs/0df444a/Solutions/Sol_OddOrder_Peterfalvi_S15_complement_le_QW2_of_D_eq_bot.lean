-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.complement_le_QW2_of_D_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:10:01.693192+00:00
-- url     : https://prove2.me/submissions/36f4cec0-4b75-42ce-907f-3546b98547e9

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch06_FrobeniusActions/OddComplement.lean
--   OddOrder/Peterfalvi/S15_SAndTBasic.lean
--   OddOrder/Peterfalvi/S15_Gate3.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Theorems.Thm_OddOrder_Isaacs_Ch06_normal_of_card_prime_of_isFrobeniusAction_of_odd
import Theorems.Thm_OddOrder_Peterfalvi_S15_Q_elementaryAbelian_T
import Theorems.Thm_OddOrder_Peterfalvi_S15_normalizer_W1_within_T_of_D_eq_bot

-- ===== OddOrder/Isaacs/Ch06_FrobeniusActions/OddComplement.lean =====
namespace OddOrder.Isaacs.Ch06

open scoped IsMulCommutative

open scoped commutatorElement

open OddOrder.Isaacs.Ch04

variable {A U : Type*} [Group A] [Finite A] [Group U] [Finite U] [Nontrivial U]
  [MulDistribMulAction A U]

/-- **Huppert V.8.18 b), subgroup-pair form.**  In a finite Frobenius group `G = N ⋊ A` whose
complement `A` has **odd order**, every subgroup `R ≤ A` of prime order is normal in `A`. -/
theorem normal_of_card_prime_of_isFrobeniusGroup_of_odd
    {G : Type*} [Group G] [Finite G] {N A : Subgroup G}
    (hFrob : IsFrobeniusGroup G N A) (hodd : Odd (Nat.card ↥A))
    {R : Subgroup ↥A} {r : ℕ} (hr : r.Prime) (hRcard : Nat.card ↥R = r) :
    R.Normal := by
  let : N.Normal := hFrob.isNormal
  let : MulDistribMulAction ↥A ↥N :=
    MulDistribMulAction.compHom ↥N ((MulAut.conjNormal (H := N)).comp A.subtype)
  have : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hFrob.ne_bot_kernel
  exact normal_of_card_prime_of_isFrobeniusAction_of_odd hFrob.toFrobeniusAction hodd hr hRcard

end OddOrder.Isaacs.Ch06

-- ===== OddOrder/Peterfalvi/S15_SAndTBasic.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.2.b)/(14.2.a), `T`-side dual of `W2_le_P`: `W₁ ≤ Q`.**  The cyclic factor `W₁`
(of prime order `q`) lies in `Q = T_F`, the maximal nilpotent normal Hall subgroup of `T`.  Dual to
`W2_le_P` (`W₂ ≤ P`), but read off the `T`-side type-`P` decomposition (`reconciled_typePData_T`)
rather than the coprime-index order count: the intrinsic dual cyclic factor
`data.W2 = C_{T'}(W₂#) = W₁` sits inside `data.H = maxNilpotentNormalHall T = Q`
(`data.W2_le`, `data.H_eq`, `Q_eq_TF`).  This is conjunct (1) of the (13.16)
`normalizer_W1_structure_of_D_eq_bot`
and is consumed by the `W₁`-side Maschke/Wielandt confinement (the dual of the `W₂`-side, where
`normalizer_U_inf_W2_eq_bot_of_data` uses `W2_le_P` at the analogous step). -/
theorem W1_le_Q [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.W1 ≤ hyp.Q := by
  obtain ⟨tpd, _, _, htpdW1⟩ := reconciled_typePData_T hG hyp
  have hHeq : tpd.H = hyp.Q := by rw [tpd.H_eq, hyp.Q_eq_TF]
  rw [← htpdW1, ← hHeq]
  exact le_trans tpd.W2_le inf_le_left

/-- **`T`-side Fitting-TI source** (Pf (13.16), dual of the `S`-side type-uniform TI result):
`F(T)^#` is a TI-subset of `G` (with normalizer `T`).

On the `W₂`-side, `normalizer_W2_le_S` reduces `N_G(W₂) ≤ S` using the type-uniform
`S13.fittingIsTI_of_isTypeNonI`.  The `W₁`-side dual applies BG Theorem 15.7(a) to `T`: the
(14.9) conclusion `IsTypeII T`, together with the BG type dictionary
`proposition_type_classification` (`IsTypeII M ↔ IsTypeP2 M`), makes `T` **type-`P₂`**, so
`fittingIsTI_of_isTypeP2` applies directly.  (The `q < p` κ-Hall ordering pins the *matched-pair*
labelling `S`/`T`, not the type: both members of a type-`P₂` pair are type-`P₂` — the earlier belief
that `T` is type-`P₁` and needed the `M_F ≠ M_σ` route was mistaken.) -/
theorem fittingIsTI_T [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) :
    OddOrder.BG.Ch4.S15.FittingIsTI hyp.T := by
  have hP2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T :=
    ((OddOrder.BG.Ch4.S16.proposition_type_classification hG hyp.T_maximal).2.1).mp hTTypeII
  exact OddOrder.BG.Ch4.S15.fittingIsTI_of_isTypeP2 hG hyp.T_maximal hP2

/-- **Peterfalvi (13.16), TI reduction for the `W₁`-side**: `N_G(W₁) ≤ T`.

The `T`-side dual of `normalizer_W2_le_S`.  `W₁ ≤ Q = T_F ≤ F(T)` (`W1_le_Q` +
`maxNilpotentNormalHall_le_fittingInG`), and `F(T)^#` is a TI-subset whose normalizer is `T`
(`fittingIsTI_T` + `normalizer_fittingInAmbient_eq_self`).  Any `g` normalizing `W₁` sends a
nonidentity `a ∈ W₁ ⊆ F(T)^#` to `g a g⁻¹ ∈ W₁ ⊆ F(T)^#`, so the TI condition places
`g ∈ N_G(F(T)) = T`.  This is the first (TI) half of the (13.16) `W₁`-confinement; the residual
`N_G(W₁) ⊓ T ≤ Q ⊔ W₂` is the Maschke/Wielandt core (the dual of `normalizer_W2_within_S`). -/
theorem normalizer_W1_le_T [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) :
    Subgroup.normalizer (hyp.W1 : Set G) ≤ hyp.T := by
  have hTI := fittingIsTI_T hG hyp hTTypeII
  have hNorm := OddOrder.BG.Ch4.S16.normalizer_fittingInAmbient_eq_self hG hyp.T_maximal
  -- `W₁ ≤ Q ≤ F(T)`.
  have hW1F : hyp.W1 ≤ OddOrder.BG.Ch4.S15.fittingInAmbient hyp.T := by
    refine (W1_le_Q hG hyp).trans ?_
    rw [hyp.Q_eq_TF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_fittingInG hyp.T
  -- a nonidentity element `a ∈ W₁` (`|W₁| = q ≥ 3`).
  have hW1ne : hyp.W1 ≠ ⊥ := by
    intro hbot
    have hq1 : hyp.q = 1 := by rw [hyp.q_eq_card_W1, hbot, Subgroup.card_bot]
    exact hyp.q_prime.one_lt.ne' hq1
  have : Nontrivial ↥hyp.W1 := (Subgroup.nontrivial_iff_ne_bot _).mpr hW1ne
  obtain ⟨x, hx1⟩ := exists_ne (1 : ↥hyp.W1)
  set a : G := (x : G) with ha
  have haW1 : a ∈ hyp.W1 := x.2
  have hane : a ≠ 1 := fun h => hx1 (OneMemClass.coe_eq_one.mp (ha ▸ h))
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg
  have hgaW1 : g * a * g⁻¹ ∈ hyp.W1 := (hg a).mp haW1
  have hgane : g * a * g⁻¹ ≠ 1 := by
    intro h
    have key : a = g⁻¹ * (g * a * g⁻¹) * g := by group
    rw [h] at key; simp only [mul_one, inv_mul_cancel] at key
    exact hane key
  have ha_sharp : a ∈ OddOrder.BG.Ch4.S15.fittingSharp hyp.T := by
    change a ∈ (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.T : Set G) \ {1}
    exact ⟨hW1F haW1, hane⟩
  have hga_sharp : g * a * g⁻¹ ∈ OddOrder.BG.Ch4.S15.fittingSharp hyp.T := by
    change g * a * g⁻¹ ∈ (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.T : Set G) \ {1}
    exact ⟨hW1F hgaW1, hgane⟩
  have hgN : g ∈ Subgroup.normalizer
      (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.T : Set G) :=
    hTI g ⟨a, ha_sharp, hga_sharp⟩
  rwa [hNorm] at hgN

/-- **Peterfalvi (13.16), structural core for the `W₁`-side** (conjunct 3 of
`normalizer_W1_structure_of_D_eq_bot`):
the Frobenius/Wielandt containment `N_G(W₁) ≤ Q ⊔ W₂`.  Assembles the TI reduction `N_G(W₁) ≤ T`
(`normalizer_W1_le_T`, proven) and the Maschke/Wielandt core `N_G(W₁) ⊓ T ≤ Q ⊔ W₂`
(`normalizer_W1_within_T_of_D_eq_bot`): every `g ∈ N_G(W₁)` lies in `T`, hence in
`N_G(W₁) ⊓ T ≤ Q ⊔ W₂`.
`T`-side dual of `normalizer_W2_structure`; gated on (14.9) `T_typeII` via the `W₁`-side core. -/
theorem normalizer_W1_le_QW2_of_D_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTTypeII : IsTypeII hyp.T) (hDbot : hyp.D = ⊥) :
    Subgroup.normalizer (hyp.W1 : Set G) ≤ hyp.Q ⊔ hyp.W2 := by
  intro g hg
  have hgT : g ∈ hyp.T := normalizer_W1_le_T hG hyp hTTypeII hg
  exact normalizer_W1_within_T_of_D_eq_bot hG hyp hTTypeII hDbot
    (Subgroup.mem_inf.mpr ⟨hg, hgT⟩)

/-- **Peterfalvi (13.16), structural core** (Coq `FTtypeP_norm_cent_compl`, `PFsection13.v:1519`),
the
three atomic facts carrying the content of (13.16), **assembled** for the (14.9) type-II member `T`:

* `W₁ ≤ Q` (`W1_le_Q`, proven) — the `T`-side dual of `W₂ ≤ P`, placing the cyclic `q`-factor `W₁`
  inside the `T`-Fitting kernel `Q = T_F`;
* `Q` abelian — from `Q_elementaryAbelian_T` (the one deep §14 σ-residual, dual of the `S`-side
  `P_elementaryAbelian`, itself once sorried and since proved);
* `N_G(W₁) ≤ Q ⊔ W₂` (`normalizer_W1_le_QW2_of_D_eq_bot`, proven) — the TI reduction
  `normalizer_W1_le_T` + the Maschke/Wielandt core `normalizer_W1_within_T_of_D_eq_bot`.

`IsTypeII T` is threaded from `exists_LHypothesis` (§16, via (14.9) `T_typeII`); conjuncts 1 and 3
are
sorry-free, so the residual is exactly conjunct 2. -/
theorem normalizer_W1_structure_of_D_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTTypeII : IsTypeII hyp.T) (hDbot : hyp.D = ⊥) :
    hyp.W1 ≤ hyp.Q ∧ IsMulCommutative ↥hyp.Q ∧
      Subgroup.normalizer (hyp.W1 : Set G) ≤ hyp.Q ⊔ hyp.W2 :=
  ⟨W1_le_Q hG hyp,
    IsMulCommutative.of_comm (Q_elementaryAbelian_T hG hyp hTTypeII).comm,
    normalizer_W1_le_QW2_of_D_eq_bot hG hyp hTTypeII hDbot⟩

/-- **Peterfalvi (13.16)**: `N_G(W₁) = C_G(W₁) = Q ⊔ W₂`.

Proved from the structural core `normalizer_W1_structure_of_D_eq_bot` by the antisymmetric chain
`Q ⊔ W₂ ≤ C_G(W₁) ≤ N_G(W₁) ≤ Q ⊔ W₂`, which collapses all three subgroups:

* `W₂ ≤ C_G(W₁)` because `W = W₁ × W₂` is abelian (`W1_commutes_W2`);
* `Q ≤ C_G(W₁)` because `W₁ ≤ Q` and `Q` is abelian (both from the core);
* `C_G(W₁) ≤ N_G(W₁)` always (`centralizer_le_normalizer`);
* `N_G(W₁) ≤ Q ⊔ W₂` is the Frobenius/Wielandt containment (the core).

Consumed by the explicit-`D = ⊥` (13.17.c) Huppert step. -/
theorem normalizer_W1_of_D_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) (hDbot : hyp.D = ⊥) :
    Subgroup.normalizer (hyp.W1 : Set G) = Subgroup.centralizer (hyp.W1 : Set G) ∧
      Subgroup.centralizer (hyp.W1 : Set G) = hyp.Q ⊔ hyp.W2 := by
  obtain ⟨hW1_le_Q, hQ_comm, hN_le⟩ :=
    normalizer_W1_structure_of_D_eq_bot hG hyp hTTypeII hDbot
  -- `W₂ ≤ C_G(W₁)`: `W = W₁ × W₂` is abelian, so `W₂` centralizes `W₁`.
  have hW2_le_C : hyp.W2 ≤ Subgroup.centralizer (hyp.W1 : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hyp.W1_commutes_W2 x (SetLike.mem_coe.mp hx) y hy
  -- `Q ≤ C_G(W₁)`: `W₁ ≤ Q` and `Q` abelian give `Q ≤ C_G(Q) ≤ C_G(W₁)`.
  have hQ_le_C : hyp.Q ≤ Subgroup.centralizer (hyp.W1 : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr hQ_comm).trans
      (Subgroup.centralizer_le (SetLike.coe_mono hW1_le_Q))
  have hQW2_le_C : hyp.Q ⊔ hyp.W2 ≤ Subgroup.centralizer (hyp.W1 : Set G) :=
    sup_le hQ_le_C hW2_le_C
  have hC_le_N : Subgroup.centralizer (hyp.W1 : Set G) ≤
      Subgroup.normalizer (hyp.W1 : Set G) := Subgroup.centralizer_le_normalizer _
  exact ⟨le_antisymm (hN_le.trans hQW2_le_C) hC_le_N,
    le_antisymm (hC_le_N.trans hN_le) hQW2_le_C⟩

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_Gate3.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.17.c), explicit-`D = ⊥` Huppert step.**  If `W₁` lies in a Frobenius
complement `E` of the type-I subgroup `L`, then `E ⊆ Q W₂`.

*Proof (Pf p.82):* `E` is a Frobenius complement of **odd** order (`E ≤ L ≤ G`, `|G|` odd), so by
Huppert ([H] Kapitel V Satz 8.18 b), `normal_of_card_prime_of_isFrobeniusGroup_of_odd`) its
prime-order subgroup `W₁` (`|W₁| = q`) is normal in `E`.  Hence `E ⊆ N_G(W₁) = C_G(W₁) = Q W₂`
by (13.16) (`normalizer_W1_of_D_eq_bot`).  This is the step of (13.17.c) consuming the new
Frobenius-complement
structure theory; the remaining order analysis (`|E| ∈ {q, p q}`, cyclic Sylows by [BG] 3.9, and
the `(14.5)` exclusion of `E = W₁`) builds on this containment. -/
theorem _root_.solution [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTTypeII : IsTypeII hyp.T) (hDbot : hyp.D = ⊥)
    {L : Subgroup G} (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW1E : hyp.W1 ≤ frob.complement.map L.subtype) :
    frob.complement.map L.subtype ≤ hyp.Q ⊔ hyp.W2 := by
  set E := frob.complement with hEdef
  -- `W₁ ≤ L`, and `W₁` (as a subgroup of `↥L`) is contained in `E`.
  have hEleL : E.map L.subtype ≤ L := Subgroup.map_subtype_le E
  have hW1L : hyp.W1 ≤ L := hW1E.trans hEleL
  have hW1L_le_E : hyp.W1.subgroupOf L ≤ E := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨e, he, hee⟩ := hW1E hx
    have hex : e = x := Subtype.coe_injective (by simpa using hee)
    rw [← hex]; exact he
  -- `R := W₁` viewed inside `E`, of prime order `q`.
  set R : Subgroup ↥E := (hyp.W1.subgroupOf L).subgroupOf E with hRdef
  have hRcard : Nat.card ↥R = hyp.q := by
    rw [hRdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1L_le_E).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1L).toEquiv]
    exact hyp.q_eq_card_W1.symm
  -- `E` has odd order (it divides `|G|`).
  have hEdvd : Nat.card ↥E ∣ Nat.card G :=
    (Subgroup.card_subgroup_dvd_card E).trans (Subgroup.card_subgroup_dvd_card L)
  have hodd : Odd (Nat.card ↥E) := _hG.odd.of_dvd_nat hEdvd
  -- Huppert V.8.18 b): `W₁` is normal in `E`, so `E` normalizes `W₁` in `↥L`.
  have hRnormal : R.Normal :=
    OddOrder.Isaacs.Ch06.normal_of_card_prime_of_isFrobeniusGroup_of_odd
      frob.frobenius hodd hyp.q_prime hRcard
  have hEnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hW1L_le_E).mp hRnormal
  -- Lift to `G`: `E.map L.subtype ≤ N_G(W₁)`.
  have hEN : E.map L.subtype ≤ Subgroup.normalizer (hyp.W1 : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    have heN := hEnorm he
    rw [Subgroup.mem_normalizer_iff] at heN ⊢
    intro w
    constructor
    · intro hw
      have hwL : w ∈ L := hW1L hw
      have hw' : (⟨w, hwL⟩ : ↥L) ∈ hyp.W1.subgroupOf L := by
        rw [Subgroup.mem_subgroupOf]; exact hw
      have hconj := ((heN ⟨w, hwL⟩).mp hw')
      rw [Subgroup.mem_subgroupOf] at hconj
      simpa using hconj
    · intro hw
      -- the conjugate lies in `W₁ ≤ L`, so `w ∈ L`, and we apply `heN` backwards.
      have he' : (L.subtype e : G) ∈ L := e.2
      have hwL : w ∈ L := by
        have hrw : w = (L.subtype e)⁻¹ * ((L.subtype e) * w * (L.subtype e)⁻¹) * (L.subtype e) := by
          group
        rw [hrw]
        exact L.mul_mem (L.mul_mem (L.inv_mem he') (hW1L hw)) he'
      have hconjmem : (e * ⟨w, hwL⟩ * e⁻¹) ∈ hyp.W1.subgroupOf L := by
        rw [Subgroup.mem_subgroupOf]; simpa using hw
      have hfin := (heN ⟨w, hwL⟩).mpr hconjmem
      rw [Subgroup.mem_subgroupOf] at hfin
      simpa using hfin
  -- (13.16): `N_G(W₁) = C_G(W₁) = Q W₂`.
  have h1316 := normalizer_W1_of_D_eq_bot _hG hyp hTTypeII hDbot
  calc E.map L.subtype ≤ Subgroup.normalizer (hyp.W1 : Set G) := hEN
    _ = Subgroup.centralizer (hyp.W1 : Set G) := h1316.1
    _ = hyp.Q ⊔ hyp.W2 := h1316.2

end OddOrder.Peterfalvi.S15

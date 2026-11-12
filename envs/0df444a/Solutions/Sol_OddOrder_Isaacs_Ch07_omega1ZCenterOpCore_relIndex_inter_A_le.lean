-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.omega1ZCenterOpCore_relIndex_inter_A_le
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:50:35.559916+00:00
-- url     : https://prove2.me/submissions/8080f9a1-da5f-4dbc-86d8-fb9c593edf86

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ_Setup.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B1_NormalJ_Setup

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ_Setup.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

private theorem zCenterOpCoreSubgroup_le_opCore
    {G : Type*} [Group G] {p : ℕ} :
    zCenterOpCoreSubgroup G p ≤ OddOrder.Isaacs.Ch01.opCore p G := by
  rintro _ ⟨⟨z, hz_L⟩, _, rfl⟩
  exact hz_L

/-- `V ≤ O_p(G)`: immediate via the chain `V ≤ Z(O_p(G)) ≤ O_p(G)`. -/
theorem omega1ZCenterOpCore_le_opCore
    {G : Type*} [Group G] {p : ℕ} :
    omega1ZCenterOpCore G p ≤ OddOrder.Isaacs.Ch01.opCore p G :=
  omega1ZCenterOpCore_le_zCenterOpCore.trans zCenterOpCoreSubgroup_le_opCore

/-- Every element of `V := Ω₁(Z(O_p(G)))` has order dividing `p`.

Pure unpacking of `mem_omega1ZCenterOpCore.2`. -/
theorem pow_p_eq_one_of_mem_omega1ZCenterOpCore
    {G : Type*} [Group G] {p : ℕ} {g : G}
    (hg : g ∈ omega1ZCenterOpCore G p) : g ^ p = 1 :=
  ((mem_omega1ZCenterOpCore).mp hg).2

/-- `V ⊆ centralizer U` in `G`: since `V ⊆ Z(U)`, every element of `V`
commutes with every element of `U`.  Used in Step 7 to argue `V * D`
is abelian (`V ⊆ centralizer U ⊇ D`). -/
theorem omega1ZCenterOpCore_centralizes_opCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    omega1ZCenterOpCore G p ≤
      Subgroup.centralizer (OddOrder.Isaacs.Ch01.opCore p G : Set G) := by
  intro x hx
  have hx_ZU : x ∈ zCenterOpCoreSubgroup G p :=
    omega1ZCenterOpCore_le_zCenterOpCore hx
  rcases hx_ZU with ⟨⟨z, hz_U⟩, hz_center, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hcomm : (⟨u, hu⟩ : ↥(OddOrder.Isaacs.Ch01.opCore p G)) * ⟨z, hz_U⟩ =
      ⟨z, hz_U⟩ * ⟨u, hu⟩ :=
    Subgroup.mem_center_iff.mp hz_center _
  exact congr_arg Subtype.val hcomm

/-- Intersection with any subgroup preserves `IsElementaryAbelian`: if `A` is
elementary abelian then `A ⊓ B` is elementary abelian.  Used in Step 7 to
get `D = A ⊓ U`, `E = A ⊓ V` elementary abelian. -/
theorem inf_isElementaryAbelian_of_isElementaryAbelian
    {G : Type*} [Group G] {p : ℕ} {A : Subgroup G} (hA : A.IsElementaryAbelian p)
    (B : Subgroup G) :
    (A ⊓ B).IsElementaryAbelian p := by
  refine ⟨?_, ?_⟩
  · rintro ⟨x, hxA, _hxB⟩ ⟨y, hyA, _hyB⟩
    apply Subtype.ext
    -- Goal in G: x * y = y * x
    have hcomm_A : (⟨x, hxA⟩ : ↥A) * ⟨y, hyA⟩ = ⟨y, hyA⟩ * ⟨x, hxA⟩ := hA.1 _ _
    exact (congr_arg (Subtype.val (p := fun x => x ∈ A)) hcomm_A : (x * y : G) = y * x)
  · rintro ⟨x, hxA, _hxB⟩
    apply Subtype.ext
    -- Goal in G: x^p = 1
    have hpow_A : (⟨x, hxA⟩ : ↥A) ^ p = 1 := hA.2 _
    exact (congr_arg (Subtype.val (p := fun x => x ∈ A)) hpow_A : (x ^ p : G) = 1)

/-- **V is elementary abelian**: every element has order dividing `p`,
and the group is commutative (it lies inside the center `Z(O_p(G))`).
Used in Step 7 (`VD` elementary abelian counting argument). -/
theorem omega1ZCenterOpCore_isElementaryAbelian
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    (omega1ZCenterOpCore G p).IsElementaryAbelian p := by
  refine ⟨omega1ZCenterOpCore_comm, ?_⟩
  intro x
  apply Subtype.ext
  change ((x : G) ^ p) = 1
  exact pow_p_eq_one_of_mem_omega1ZCenterOpCore x.2

end OddOrder.Isaacs.Ch07

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Subgroup `V ⊔ D` is contained in its own centralizer** when `V`
centralizes `D`, `V` is commutative, and `D` is commutative.

This packages `V ⊔ D ≤ centralizer (V ⊔ D)`, i.e., `V ⊔ D` is abelian. -/
private theorem sup_le_centralizer_self_of_centralizing
    {G : Type*} [Group G] {V D : Subgroup G}
    (hV_comm : ∀ x y : ↥V, x * y = y * x)
    (hD_comm : ∀ x y : ↥D, x * y = y * x)
    (hVD : V ≤ Subgroup.centralizer (D : Set G)) :
    (V ⊔ D : Subgroup G) ≤ Subgroup.centralizer ((V ⊔ D : Subgroup G) : Set G) := by
  -- Strategy: show V ∪ D ⊆ centralizer (V ⊔ D), then by closure of centralizer.
  -- centralizer is a subgroup, so closure (V ∪ D) ⊆ centralizer (V ⊔ D).
  -- V ⊔ D = closure (V ∪ D), giving the conclusion.
  have h_VuD_in_cent : (V : Set G) ∪ (D : Set G) ⊆
      Subgroup.centralizer ((V ⊔ D : Subgroup G) : Set G) := by
    -- Show each element of V ∪ D commutes with every element of V ⊔ D.
    intro w hw
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro x hx
    -- x ∈ V ⊔ D ⟺ x ∈ closure (V ∪ D). Use closure_induction.
    have hx_clos : x ∈ Subgroup.closure ((V : Set G) ∪ (D : Set G)) := by
      rwa [← Subgroup.sup_eq_closure]
    clear hx
    -- w ∈ V ∪ D, x ∈ closure (V ∪ D). Goal: x * w = w * x.
    induction hx_clos using Subgroup.closure_induction with
    | mem y hy =>
      -- Both w and y are in V ∪ D, show they commute.
      rcases hw with hw_V | hw_D
      · rcases hy with hy_V | hy_D
        · have := hV_comm ⟨y, hy_V⟩ ⟨w, hw_V⟩
          exact congr_arg Subtype.val this
        · -- w ∈ V, y ∈ D: hVD says V centralizes D.
          have h_w_cent := hVD hw_V
          rw [Subgroup.mem_centralizer_iff] at h_w_cent
          exact h_w_cent y hy_D
      · rcases hy with hy_V | hy_D
        · -- w ∈ D, y ∈ V: hVD says V centralizes D.
          have h_y_cent := hVD hy_V
          rw [Subgroup.mem_centralizer_iff] at h_y_cent
          exact (h_y_cent w hw_D).symm
        · have := hD_comm ⟨y, hy_D⟩ ⟨w, hw_D⟩
          exact congr_arg Subtype.val this
    | one => rw [one_mul, mul_one]
    | mul a b _ _ ha hb =>
      calc (a * b) * w = a * (b * w) := by group
        _ = a * (w * b) := by rw [hb]
        _ = (a * w) * b := by group
        _ = (w * a) * b := by rw [ha]
        _ = w * (a * b) := by group
    | inv a _ ha =>
      have hcomm : a * w = w * a := ha
      calc a⁻¹ * w = a⁻¹ * (w * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * w) * a⁻¹ := by rw [hcomm]
        _ = w * a⁻¹ := by group
  -- Now centralizer is a subgroup, so closure (V ∪ D) ⊆ centralizer (V ⊔ D).
  -- The result follows because V ⊔ D = closure (V ∪ D).
  intro x hx
  -- Convert hx to closure form, apply h_VuD_in_cent + closure_le.
  have hx_clos : x ∈ Subgroup.closure ((V : Set G) ∪ (D : Set G)) := by
    rwa [← Subgroup.sup_eq_closure]
  exact (Subgroup.closure_le _).mpr h_VuD_in_cent hx_clos

/-- **VD is elementary abelian**: if `V` centralizes `D`, both `V` and `D` are
elementary abelian `p`-groups, and `V` is normal in `G`, then `V ⊔ D` is also
elementary abelian.

Proof: by `mul_normal`, every element of `V ⊔ D` is `v * d` for some `v ∈ V`,
`d ∈ D`.  Commutativity in `V ⊔ D` and exponent `p` both follow from `V` and
`D` commuting pointwise. -/
private theorem sup_isElementaryAbelian_of_centralizing
    {G : Type*} [Group G] {p : ℕ} {V D : Subgroup G} [V.Normal]
    (hV : V.IsElementaryAbelian p) (hD : D.IsElementaryAbelian p)
    (hVD : V ≤ Subgroup.centralizer (D : Set G)) :
    (V ⊔ D : Subgroup G).IsElementaryAbelian p := by
  have h_VD_comm : (V ⊔ D : Subgroup G) ≤
      Subgroup.centralizer ((V ⊔ D : Subgroup G) : Set G) :=
    sup_le_centralizer_self_of_centralizing hV.1 hD.1 hVD
  -- Element decomposition: every element of V ⊔ D is v*d for v ∈ V, d ∈ D.
  have h_decomp : ∀ x ∈ (V ⊔ D : Subgroup G), ∃ v ∈ V, ∃ d ∈ D, (v * d : G) = x := by
    intro x hx
    have h_mul : (↑(V ⊔ D) : Set G) = V * D := Subgroup.normal_mul V D
    have hx_set : x ∈ (↑(V ⊔ D) : Set G) := hx
    rw [h_mul] at hx_set
    obtain ⟨v, hv, d, hd, hvd⟩ := hx_set
    exact ⟨v, hv, d, hd, hvd⟩
  refine ⟨?_, ?_⟩
  · -- Commutativity in V ⊔ D.
    intro x y
    apply Subtype.ext
    have hxy_cent := h_VD_comm x.2
    rw [Subgroup.mem_centralizer_iff] at hxy_cent
    have : (y : G) * x = x * y := hxy_cent y y.2
    exact this.symm
  · -- Exponent p.  In V ⊔ D, every element w has w^p = 1.
    intro w
    apply Subtype.ext
    change (w.val : G) ^ p = 1
    -- w = v * d for some v ∈ V, d ∈ D.
    obtain ⟨v, hv_V, d, hd_D, hvd_eq⟩ := h_decomp w.val w.2
    rw [← hvd_eq]
    -- (v * d)^p = v^p * d^p (since v and d commute), and v^p = 1, d^p = 1.
    have hv_d_comm : v * d = d * v := by
      have hv_cent := hVD hv_V
      rw [Subgroup.mem_centralizer_iff] at hv_cent
      exact (hv_cent d hd_D).symm
    have hCom : Commute v d := hv_d_comm
    have : (v * d) ^ p = v ^ p * d ^ p := Commute.mul_pow hCom p
    rw [this]
    have hv_p : v ^ p = 1 := by
      have := hV.2 ⟨v, hv_V⟩
      exact congr_arg Subtype.val this
    have hd_p : d ^ p = 1 := by
      have := hD.2 ⟨d, hd_D⟩
      exact congr_arg Subtype.val this
    rw [hv_p, hd_p, mul_one]

/-- **Isaacs Thm 7.6 Step 7** (mmd L3886-3892): `|V : V ∩ A| ≤ p` for any
`A ∈ maxElemAbelianIn P p`, assuming `|A : A ∩ U| ≤ p` (Step 5).

`A.relIndex V` is `|V : V ⊓ A|` in book notation
(`(A.subgroupOf V).index = |V/(A ⊓ V)|`).  Similarly,
`(A ⊓ U).relIndex A = |A : A ⊓ U|` is the Step-5 bound.

The book's argument:
1. Set `D = U ∩ A` and `E = V ∩ A`.  Observe `V ⊆ U` (so `V ∩ A = V ∩ D`).
2. `D` is elementary abelian (sub of `A`).
3. `V` is elementary abelian and central in `U`, so `V ⊆ centralizer D`.
4. `VD := V ⊔ D` is elementary abelian (`sup_isElementaryAbelian_of_centralizing`).
5. `VD ≤ P` (since `V ≤ U ≤ P` and `D ≤ A ≤ P`).
6. By maximality `A ∈ E(P)`, `|VD| ≤ |A|`, so `|VD : D| ≤ |A : D|`.
7. By second isomorphism (V normal, V centralizes D), `|V : V ∩ D| = |VD : D|`.
8. Combine: `|V : V ∩ A| = |V : V ∩ D| = |VD : D| ≤ |A : D| ≤ p`. -/
theorem _root_.solution
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {A : Subgroup G}
    (hA : A ∈ Subgroup.maxElemAbelianIn (P : Subgroup G) p)
    (hA_D_relIndex : (OddOrder.Isaacs.Ch01.opCore p G).relIndex A ≤ p) :
    A.relIndex (omega1ZCenterOpCore G p) ≤ p := by
  classical
  set V : Subgroup G := omega1ZCenterOpCore G p with hV_def
  set U : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hU_def
  set D : Subgroup G := A ⊓ U with hD_def
  -- Basic facts.
  have hV_le_U : V ≤ U := omega1ZCenterOpCore_le_opCore
  have hA_P : A ≤ (P : Subgroup G) := hA.1
  have hU_P : U ≤ (P : Subgroup G) := OddOrder.Isaacs.Ch01.opCore_le P
  have hA_el : A.IsElementaryAbelian p := hA.2.1
  have hD_el : D.IsElementaryAbelian p :=
    inf_isElementaryAbelian_of_isElementaryAbelian hA_el U
  have hV_el : V.IsElementaryAbelian p := omega1ZCenterOpCore_isElementaryAbelian
  have hV_cent_U : V ≤ Subgroup.centralizer (U : Set G) :=
    omega1ZCenterOpCore_centralizes_opCore
  have hD_le_U : D ≤ U := inf_le_right
  have hD_le_A : D ≤ A := inf_le_left
  have hV_cent_D : V ≤ Subgroup.centralizer (D : Set G) :=
    hV_cent_U.trans (Subgroup.centralizer_le hD_le_U)
  -- V ⊔ D is elementary abelian.
  have : V.Normal := omega1ZCenterOpCore_normal
  have hVD_el : (V ⊔ D : Subgroup G).IsElementaryAbelian p :=
    sup_isElementaryAbelian_of_centralizing hV_el hD_el hV_cent_D
  -- V ⊔ D ≤ P.
  have hVD_le_P : (V ⊔ D : Subgroup G) ≤ (P : Subgroup G) := by
    rw [sup_le_iff]
    exact ⟨hV_le_U.trans hU_P, hD_le_A.trans hA_P⟩
  -- Maximality of A: |V ⊔ D| ≤ |A|.
  have hVD_card_le_A : Nat.card (V ⊔ D : Subgroup G) ≤ Nat.card A :=
    hA.2.2 (V ⊔ D) hVD_le_P hVD_el
  -- A.relIndex V = |V : V ∩ A| (book notation).  Rewrite via V ⊓ A = V ⊓ D.
  -- V ⊓ A = V ⊓ U ⊓ A = V ⊓ (U ⊓ A) = V ⊓ (A ⊓ U) = V ⊓ D since V ≤ U.
  have hVA_eq_VD : V ⊓ A = V ⊓ D := by
    have h_VU : V ⊓ U = V := inf_eq_left.mpr hV_le_U
    rw [hD_def, inf_comm A U, ← inf_assoc, h_VU]
  have hAV_eq : A.relIndex V = D.relIndex V := by
    -- A.relIndex V = (A ⊓ V).relIndex V via inf_relIndex_right.
    -- Same for D. Use V ⊓ A = V ⊓ D, i.e., A ⊓ V = D ⊓ V (by inf_comm).
    have h1 : A.relIndex V = (A ⊓ V).relIndex V := (Subgroup.inf_relIndex_right A V).symm
    have h2 : D.relIndex V = (D ⊓ V).relIndex V := (Subgroup.inf_relIndex_right D V).symm
    have h_inf_comm : A ⊓ V = D ⊓ V := by
      rw [inf_comm A V, inf_comm D V]; exact hVA_eq_VD
    rw [h1, h2, h_inf_comm]
  rw [hAV_eq]
  -- Second isomorphism: V / (D ⊓ V) ≅ (V ⊔ D) / D, requiring V ≤ normalizer D.
  -- V centralizes D, so V ≤ centralizer D ≤ normalizer D.
  have hV_norm_D : V ≤ Subgroup.normalizer D := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hv_cent : v ∈ Subgroup.centralizer (D : Set G) := hV_cent_D hv
    have hv_inv_cent : v⁻¹ ∈ Subgroup.centralizer (D : Set G) := Subgroup.inv_mem _ hv_cent
    constructor
    · intro hy
      have hyv : y * v = v * y := Subgroup.mem_centralizer_iff.mp hv_cent y hy
      have heq : v * y * v⁻¹ = y := by
        calc v * y * v⁻¹ = (y * v) * v⁻¹ := by rw [hyv]
          _ = y := by group
      rw [heq]
      exact hy
    · intro hyc
      have hcomm := Subgroup.mem_centralizer_iff.mp hv_inv_cent (v * y * v⁻¹) hyc
      have heq : y = v⁻¹ * (v * y * v⁻¹) * v := by group
      have hpush : v⁻¹ * (v * y * v⁻¹) * v = v * y * v⁻¹ := by
        calc v⁻¹ * (v * y * v⁻¹) * v
            = (v * y * v⁻¹) * v⁻¹ * v := by rw [← hcomm]
          _ = v * y * v⁻¹ := by group
      rw [heq, hpush]
      exact hyc
  set VD : Subgroup G := V ⊔ D with hVD_def
  have hD_le_VD : D ≤ VD := hVD_def ▸ le_sup_right
  -- Apply second iso: |V/(D ⊓ V).subgroupOf V| = |VD/D.subgroupOf VD|.
  let hD_normal_in_V : (D.subgroupOf V).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hV_norm_D
  let hD_normal_in_VD : (D.subgroupOf VD).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hV_norm_D
  have h_card_quot_V : Nat.card (V ⧸ D.subgroupOf V) =
      Nat.card (VD ⧸ D.subgroupOf VD) :=
    Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient V D hV_norm_D).toEquiv
  have h_card_eq : D.relIndex V = D.relIndex VD := by
    unfold Subgroup.relIndex Subgroup.index
    exact h_card_quot_V
  rw [h_card_eq]
  -- Lagrange: |VD| = D.relIndex VD * |D|, |A| = U.relIndex A * |D|.
  have hD_card_pos : 0 < Nat.card D := Nat.card_pos
  have h_lag_VD : Nat.card VD = D.relIndex VD * Nat.card D := by
    have h_index_mul_card : (D.subgroupOf VD).index *
        Nat.card (D.subgroupOf VD) = Nat.card VD :=
      Subgroup.index_mul_card _
    have hD_card_eq : Nat.card (D.subgroupOf VD) = Nat.card D := by
      have h_map_eq : ((D.subgroupOf VD : Subgroup VD).map VD.subtype : Subgroup G) = D :=
        Subgroup.map_subgroupOf_eq_of_le hD_le_VD
      have h_card : Nat.card (D.subgroupOf VD) =
          Nat.card ((D.subgroupOf VD : Subgroup VD).map VD.subtype) :=
        (Subgroup.card_map_of_injective VD.subtype_injective).symm
      rw [h_card, h_map_eq]
    rw [show D.relIndex VD = (D.subgroupOf VD).index from rfl,
        ← h_index_mul_card, hD_card_eq]
  have h_lag_A : Nat.card A = U.relIndex A * Nat.card D := by
    have h_index_mul_card : (U.subgroupOf A).index *
        Nat.card (U.subgroupOf A) = Nat.card A :=
      Subgroup.index_mul_card _
    have hU_subgrpOf_card : Nat.card (U.subgroupOf A) = Nat.card D := by
      -- (U.subgroupOf A).map A.subtype = U ⊓ A = A ⊓ U = D.
      have h_map_eq : ((U.subgroupOf A : Subgroup A).map A.subtype : Subgroup G) = U ⊓ A :=
        Subgroup.subgroupOf_map_subtype U A
      have h_card : Nat.card (U.subgroupOf A) =
          Nat.card ((U.subgroupOf A : Subgroup A).map A.subtype) :=
        (Subgroup.card_map_of_injective A.subtype_injective).symm
      rw [h_card, h_map_eq, inf_comm, ← hD_def]
    rw [show U.relIndex A = (U.subgroupOf A).index from rfl,
        ← h_index_mul_card, hU_subgrpOf_card]
  -- D.relIndex VD * |D| = |VD| ≤ |A| = U.relIndex A * |D|.
  have hVD_card_le_A' : Nat.card VD ≤ Nat.card A := hVD_card_le_A
  have hmul_le : D.relIndex VD * Nat.card D ≤ U.relIndex A * Nat.card D := by
    rw [← h_lag_VD, ← h_lag_A]
    exact hVD_card_le_A'
  exact (Nat.le_of_mul_le_mul_right hmul_le hD_card_pos).trans hA_D_relIndex

end OddOrder.Isaacs.Ch07

-- Prove2me | solution 1 for OddOrder.Isaacs.Ch05.OPrime_meet_sylow_eq_bot_of_controlsOwnFusion
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:32:49.821357+00:00
-- url     : https://prove2.me/submissions/f305e4b3-e456-48aa-b430-80d83fcca882

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch05_Transfer/Basic.lean
--   OddOrder/Isaacs/Ch05_Transfer/Main.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_CyclicSubgroupUniqueness
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Main
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorBasics
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ChainNilpotent
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups
import Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Basic
import Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Main
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Focal
import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Nilpotent
import Theorems.Thm_OddOrder_Isaacs_Ch05_OPrime_index_isPGroup
import Theorems.Thm_OddOrder_Isaacs_Ch05_APrime_index_isPGroup

-- ===== OddOrder/Isaacs/Ch05_Transfer/Basic.lean =====
open scoped commutatorElement

open scoped IsMulCommutative

namespace OddOrder.Isaacs.Ch05

open Pointwise

open scoped commutatorElement

variable {G : Type*} [Group G]

section

/-- `OPrime p G` ≤ any normal subgroup with `p`-power index. -/
lemma OPrime_le {p : ℕ} {G : Type*} [Group G] {N : Subgroup G}
    (hN_normal : N.Normal) {k : ℕ} (hN_idx : N.index = p ^ k) :
    OPrime p G ≤ N :=
  iInf_le_of_le ⟨N, hN_normal, k, hN_idx⟩ le_rfl

/-- `APrime p G` ≤ any normal subgroup containing `commutator G` with p-power index. -/
lemma APrime_le {p : ℕ} {G : Type*} [Group G] {K : Subgroup G}
    (hN : K.Normal) (hC : commutator G ≤ K) {k : ℕ} (hi : K.index = p ^ k) :
    APrime p G ≤ K :=
  iInf_le_of_le ⟨K, hN, hC, k, hi⟩ le_rfl

/-- `commutator G ≤ APrime p G` (the commutator is contained in every family member). -/
lemma commutator_le_APrime (p : ℕ) (G : Type*) [Group G] : commutator G ≤ APrime p G := by
  intro x hx
  unfold APrime
  rw [Subgroup.mem_iInf]
  intro K
  exact K.property.2.1 hx

/-- For finite groups, `A^p(G)` is characteristic.

This is the automorphism-invariance of Isaacs' defining family: normal subgroups containing
`G'` with p-power index are preserved by every automorphism. -/
lemma APrime_characteristic (p : ℕ) (G : Type*) [Group G] [Finite G] [Fact p.Prime] :
    (APrime p G).Characteristic := by
  classical
  rw [Subgroup.characteristic_iff_le_comap]
  intro φ
  let K : Subgroup G := (APrime p G).comap φ.toMonoidHom
  have hK_normal : K.Normal := inferInstance
  have hK_comm : commutator G ≤ K := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hxmap : φ x ∈ (commutator G).map φ.toMonoidHom :=
      Subgroup.mem_map_of_mem φ.toMonoidHom hx
    have hmap_comm : (commutator G).map φ.toMonoidHom = commutator G := by
      rw [_root_.map_commutator_eq,
        φ.toMonoidHom.range_eq_top_of_surjective φ.surjective,
        ← _root_.commutator_def]
    exact commutator_le_APrime p G (hmap_comm ▸ hxmap)
  obtain ⟨k, hk⟩ := APrime_index_isPGroup p G
  have hK_index : K.index = p ^ k := by
    rw [Subgroup.index_comap_of_surjective (H := APrime p G)
      (f := φ.toMonoidHom) φ.surjective, hk]
  exact APrime_le (K := K) hK_normal hK_comm hK_index

/-- The transfer-focal kernel contains `A^p(G)`.

This is the `A^p` half of Isaacs Thm 5.21 in the mathlib formulation: the quotient
`G / ker(V)` is isomorphic to the p-group `P / P*`, and `ker(V)` contains `G'`. -/
lemma APrime_le_transferFocal_ker [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) : APrime p G ≤ P.transferFocal.ker := by
  classical
  have hquot : IsPGroup p (G ⧸ P.transferFocal.ker) :=
    (P.2.to_quotient P.focalSubgroupOf).of_equiv
      (Subgroup.transferFocal.quotientKerMulEquivQuotientFocalSubroupOf P).symm
  obtain ⟨k, hk⟩ := hquot.exists_card_eq
  have hker_index : P.transferFocal.ker.index = p ^ k := by
    rw [Subgroup.index_eq_card]
    exact hk
  exact APrime_le (K := P.transferFocal.ker) inferInstance
    (Abelianization.commutator_subset_ker P.transferFocal) hker_index

end

end OddOrder.Isaacs.Ch05

-- ===== OddOrder/Isaacs/Ch05_Transfer/Main.lean =====
open scoped commutatorElement

open scoped IsMulCommutative

namespace OddOrder.Isaacs.Ch05

open Pointwise

open scoped commutatorElement

variable {G : Type*} [Group G]

section

/-- If `A^p(G)=G`, then a Sylow p-subgroup is equal to its focal subgroup.

This packages only the standard `A^p` consequence of the focal subgroup theorem, avoiding a
separate public bridge through `G'`. -/
lemma sylow_focalSubgroup_eq_self_of_APrime_eq_top [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hA : APrime p G = ⊤) :
    P.focalSubgroup = (P : Subgroup G) := by
  have hker_top : P.transferFocal.ker = ⊤ := by
    apply eq_top_iff.mpr
    simpa [hA] using APrime_le_transferFocal_ker (G := G) (p := p) P
  rw [← Subgroup.ker_transferFocal_inf_eq_focalSubgroup P, hker_top, top_inf_eq]

/-- **Isaacs Thm 5.25 proof step**: if `N = O^p(G)`, then `A^p(N)=N`.

Isaacs p.173 uses that `A^p(N)` is characteristic in `N`, hence normal in `G`, and that
`|G:A^p(N)| = |G:N| · |N:A^p(N)|` is a p-power. Minimality of `O^p(G)` then gives
`N ≤ A^p(N).map subtype ≤ N`, so `A^p(N)=N` internally. -/
lemma APrime_eq_top_of_eq_OPrime [Finite G] {p : ℕ} [Fact p.Prime]
    {N : Subgroup G} [N.Normal] (hN : N = OPrime p G) :
    APrime p N = ⊤ := by
  classical
  let A : Subgroup N := APrime p N
  have hA_char : A.Characteristic := by
    simpa [A] using APrime_characteristic (p := p) (G := N)
  have hAmap_normal : (A.map N.subtype).Normal := inferInstance
  have hAmap_le_N : A.map N.subtype ≤ N :=
    Subgroup.map_subtype_le A
  obtain ⟨a, hN_index⟩ : ∃ a : ℕ, N.index = p ^ a := by
    rw [hN]
    exact OPrime_index_isPGroup p G
  obtain ⟨b, hA_index⟩ : ∃ b : ℕ, A.index = p ^ b := by
    simpa [A] using APrime_index_isPGroup p N
  have hAmap_index : (A.map N.subtype).index = p ^ (b + a) := by
    rw [Subgroup.index_map_subtype, hA_index, hN_index, ← pow_add]
  have hN_le_Amap : N ≤ A.map N.subtype := by
    have hO_le_Amap : OPrime p G ≤ A.map N.subtype :=
      OPrime_le hAmap_normal hAmap_index
    exact hN.symm ▸ hO_le_Amap
  have hAmap_eq_N : A.map N.subtype = N :=
    le_antisymm hAmap_le_N hN_le_Amap
  have hA_eq_top : A = ⊤ := by
    apply (Subgroup.map_subtype_inj (H := N)).mp
    rw [hAmap_eq_N, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  simpa [A] using hA_eq_top

/-- **Helper for Thm 5.25 (⇐)**: heart of the proof. Sylow_p `P` that controls its own G-fusion
satisfies `P ⊓ OPrime p G = ⊥`. The rest of Thm 5.25 (⇐) is a Sylow-conjugacy + cardinality
assembly on top of this.

**証明スケッチ** (Isaacs p.173):
* `N := OPrime p G`. `Q := (P ⊓ N).subgroupOf N` is Sylow `p` of `↥N` (cardinality argument:
  `|P ⊓ N| = |P| / [G : N · P]` and `N · P = G` from `[G:N]` being p-power dividing `|P|`).
* **APrime p ↥N = ⊤**: `APrime p ↥N` is characteristic in `↥N` (Aut(N) preserves the
  defining family) ⇒ its `.map N.subtype` is normal in `G`. It has p-power index in `G`
  (= `|G:N| · |↥N : APrime|`), so by `OPrime` minimality `N ≤ (APrime).map subtype ≤ N`,
  hence equality, hence `APrime p ↥N = ⊤` in `↥N`.
* **Focal Subgroup Theorem**: `APrime p ↥N = ⊤` and transfer-focal give
  `focalSubgroup Q = Q`. This is the `A^p(N)=N` line in Isaacs followed by Thm 5.21,
  without adding an extra public bridge through `commutator ↥N`.
* **ControlsOwnFusion lift**: every generator `⁅x, u⁆ ∈ focalSubgroup Q` (with `x ∈ Q`,
  `u ∈ ↥N` such that `[x,u] ∈ Q`) can be rewritten using ControlsOwnFusion. Set
  `y := u x u⁻¹ ∈ Q ⊆ P`; controlsOwnFusion gives `v ∈ P` with `v x v⁻¹ = y`. Then
  `[x, v⁻¹] = x⁻¹ y` is in `⁅Q.map N.subtype, (P : Subgroup G)⁆`. Hence
  `focalSubgroup Q ≤ ⁅Q.map subtype, P⁆` (viewing all in `G`).
* **Iteration**: Combine the previous two: `Q.map subtype ≤ ⁅Q.map subtype, P⁆` in `G`. By
  induction on `n`, `Q.map subtype ≤ lowerCentralSeries (P : Subgroup G) n`.
  (Base: `Q.map subtype ≤ P` since `Q ⊆ P`. Step: `Q.map subtype ≤ ⁅Q.map subtype, P⁆ ≤
  ⁅lowerCentralSeries P n, ⊤⁆ = lowerCentralSeries P (n+1)`.)
* **Termination**: `P` is a finite p-group ⇒ `IsNilpotent P` (`IsPGroup.isNilpotent`) ⇒
  `∃ n, lowerCentralSeries P n = ⊥` (`Subgroup.nilpotent_iff_lowerCentralSeries`). Hence
  `Q.map subtype = ⊥` in `G`, so `(P : Subgroup G) ⊓ N = ⊥`.

The proof below implements these steps directly. -/
theorem _root_.solution [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hP : P.ControlsOwnFusion) :
    (P : Subgroup G) ⊓ OPrime p G = ⊥ := by
  set N : Subgroup G := OPrime p G with hN_def
  have hN_normal : N.Normal := inferInstance
  set R : Subgroup G := (P : Subgroup G) ⊓ N with hR_def
  have hR_le_P : R ≤ (P : Subgroup G) := by
    rw [hR_def]
    exact inf_le_left
  -- Controls-own-fusion converts focal generators of `R` into commutators with `P`.
  have h_focal_R_le_comm : R.focalSubgroup ≤ ⁅R, (P : Subgroup G)⁆ := by
    rw [Subgroup.focalSubgroup_def, Subgroup.closure_le]
    rintro g ⟨hgR, x, hxR, u, rfl⟩
    have hyR : u * x * u⁻¹ ∈ R := by
      have hy_eq : u * x * u⁻¹ = (⁅x, u⁆)⁻¹ * x := by
        rw [commutatorElement_def]
        group
      rw [hy_eq]
      exact R.mul_mem (R.inv_mem hgR) hxR
    obtain ⟨v, hvP, hv⟩ := hP (hR_le_P hxR) (hR_le_P hyR) ⟨u, rfl⟩
    have hcomm_eq : ⁅x, u⁆ = ⁅x, v⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc
        x * u * x⁻¹ * u⁻¹ = x * (u * x * u⁻¹)⁻¹ := by group
        _ = x * (v * x * v⁻¹)⁻¹ := by rw [hv]
        _ = x * v * x⁻¹ * v⁻¹ := by group
    rw [hcomm_eq]
    exact Subgroup.commutator_mem_commutator hxR hvP
  -- **Crux**: `R ≤ ⁅R, (P : Subgroup G)⁆`.
  -- 内訳: APrime ↥N = ⊤ (char + OPrime minimality) → transfer-focal で
  -- focalSubgroup Q = Q → 各 focal generator ⁅x, u⁆ (x ∈ Q, u ∈ ↥N) を
  -- ControlsOwnFusion で ⁅Q.map subtype, P⁆ 内 commutator に変換.
  have h_R_le_comm : R ≤ ⁅R, (P : Subgroup G)⁆ := by
    have h_R_le_focal : R ≤ R.focalSubgroup := by
      have hR_le_N : R ≤ N := by
        rw [hR_def]
        exact inf_le_right
      have hR_pgroup : IsPGroup p R :=
        P.isPGroup'.to_le hR_le_P
      have hRN_pgroup : IsPGroup p (R.subgroupOf N) :=
        hR_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hR_le_N).symm
      have hRN_not_dvd : ¬ p ∣ (R.subgroupOf N).index := by
        obtain ⟨a, hN_idx_pow⟩ : ∃ a : ℕ, N.index = p ^ a := by
          rw [hN_def]
          exact OPrime_index_isPGroup p G
        have hNP_coprime : Nat.Coprime N.index (P : Subgroup G).index := by
          rw [hN_idx_pow]
          exact (Nat.Prime.coprime_pow_of_not_dvd (m := a) Fact.out P.not_dvd_index).symm
        have hNP_top : N ⊔ (P : Subgroup G) = ⊤ :=
          OddOrder.Isaacs.Ch03.sup_eq_top_of_coprime_index hNP_coprime
        have h_index_eq : (R.subgroupOf N).index = (P : Subgroup G).index := by
          have hR_le_N' : R ≤ N := hR_le_N
          have hR_rel_mul : R.relIndex N * N.index = R.index :=
            Subgroup.relIndex_mul_index hR_le_N'
          have hN_rel_P : N.relIndex (P : Subgroup G) = N.index := by
            rw [← Subgroup.relIndex_sup_right (H := (P : Subgroup G)) (K := N),
              sup_comm, hNP_top, Subgroup.relIndex_top_right]
          have hNP_rel_mul : N.relIndex (P : Subgroup G) * (P : Subgroup G).index =
              R.index := by
            have h := Subgroup.relIndex_inf_mul_relIndex (H := N)
              (K := (P : Subgroup G)) (L := (⊤ : Subgroup G))
            simpa [Subgroup.relIndex_top_right, hR_def, inf_comm] using h
          have hmul : R.relIndex N * N.index = (P : Subgroup G).index * N.index := by
            rw [hR_rel_mul, ← hNP_rel_mul, hN_rel_P, mul_comm N.index]
          have hrel : R.relIndex N = (P : Subgroup G).index :=
            Nat.eq_of_mul_eq_mul_right
              (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hmul
          exact hrel
        rw [h_index_eq]
        exact P.not_dvd_index
      let RN : Sylow p N := hRN_pgroup.toSylow hRN_not_dvd
      have hRN_eq : (RN : Subgroup N) = R.subgroupOf N :=
        hRN_pgroup.toSylow_coe hRN_not_dvd
      have hAPrime_top : APrime p N = ⊤ :=
        APrime_eq_top_of_eq_OPrime (G := G) (p := p) (N := N) hN_def
      have hRN_focal_eq : RN.focalSubgroup = (RN : Subgroup N) :=
        sylow_focalSubgroup_eq_self_of_APrime_eq_top RN hAPrime_top
      have hRN_le_focal : R.subgroupOf N ≤ RN.focalSubgroup := by
        intro x hx
        rw [hRN_focal_eq, hRN_eq]
        exact hx
      have hRN_focal_map_le : RN.focalSubgroup.map N.subtype ≤ R.focalSubgroup := by
        rw [Subgroup.focalSubgroup_def, MonoidHom.map_closure, Subgroup.focalSubgroup_def]
        apply Subgroup.closure_mono
        rintro y ⟨z, hz, rfl⟩
        rcases hz with ⟨hzRN, x, hxRN, u, rfl⟩
        have hzR : ((⁅x, u⁆ : N) : G) ∈ R := hzRN
        have hxR : (x : G) ∈ R := by
          have hxRN' : x ∈ R.subgroupOf N := by
            rwa [hRN_eq] at hxRN
          exact hxRN'
        exact ⟨hzR, (x : G), hxR, (u : G), rfl⟩
      intro r hr
      let x : N := ⟨r, hR_le_N hr⟩
      have hxRN : x ∈ R.subgroupOf N := hr
      have hxFocal : x ∈ RN.focalSubgroup := hRN_le_focal hxRN
      exact hRN_focal_map_le (Subgroup.mem_map_of_mem N.subtype hxFocal)
    exact h_R_le_focal.trans h_focal_R_le_comm
  -- Helper: `(⊤ : Subgroup ↥P).map P.subtype = P` (via `range_eq_map` + `range_subtype`).
  have h_top_map : ((⊤ : Subgroup ↥(P : Subgroup G))).map (P : Subgroup G).subtype =
      (P : Subgroup G) := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  -- **Step 5 (iteration)**: `∀ n, R ≤ ((⊤ : Subgroup ↥P).lowerCentralSeries n).map P.subtype`.
  -- Base: R ⊆ P = ⊤.map subtype. Step: R ≤ ⁅R, P⁆ = ⁅R, ⊤.map subtype⁆ ≤ ⁅(lcs n).map, ⊤.map⁆
  --       = (⁅lcs n, ⊤⁆).map = (lcs (n+1)).map.
  have h_R_le_lcs : ∀ n : ℕ, R ≤ Subgroup.map (P : Subgroup G).subtype
      ((⊤ : Subgroup ↥(P : Subgroup G)).lowerCentralSeries n) := by
    intro n
    induction n with
    | zero =>
      change R ≤ Subgroup.map (P : Subgroup G).subtype ⊤
      rw [h_top_map]
      exact inf_le_left
    | succ n ih =>
      change R ≤ Subgroup.map (P : Subgroup G).subtype
        ⁅(⊤ : Subgroup ↥(P : Subgroup G)).lowerCentralSeries n,
          (⊤ : Subgroup ↥(P : Subgroup G))⁆
      rw [Subgroup.map_commutator, h_top_map]
      exact h_R_le_comm.trans (Subgroup.commutator_mono ih le_rfl)
  -- **Step 6 (termination)**: `P` is a finite p-group ⇒ nilpotent ⇒ `∃ n, lcs ↥P n = ⊥`.
  have hP_pgroup : IsPGroup p ↥(P : Subgroup G) := P.isPGroup'
  have hP_nilp : Group.IsNilpotent ↥(P : Subgroup G) := hP_pgroup.isNilpotent
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hP_nilp
  have : R ≤ ⊥ := by
    have := h_R_le_lcs n
    rw [hn, Subgroup.map_bot] at this
    exact this
  exact le_bot_iff.mp this

end

end OddOrder.Isaacs.Ch05

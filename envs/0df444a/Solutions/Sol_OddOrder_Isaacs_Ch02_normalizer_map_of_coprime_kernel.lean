-- Prove2me | solution 1 for OddOrder.Isaacs.Ch02.normalizer_map_of_coprime_kernel
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T04:54:12.808242+00:00
-- url     : https://prove2.me/submissions/f8084a57-9639-4a1e-aaa9-254b586f7ec8

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch02_Subnormality/Main.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch02_Subnormality_Theorem211Wielandt

-- ===== OddOrder/Isaacs/Ch02_Subnormality/Main.lean =====
open OddOrder.Isaacs.Ch01

namespace OddOrder.Isaacs.Ch02

section

variable {G : Type*} [Group G]

set_option maxHeartbeats 1200000 in
-- 長い構成的証明 (Sylow II + Frattini, ↥M 内で構築 + G への持ち上げ) のため heartbeat を増やす.
/-- **Isaacs Lemma 2.17 (image of normalizer under p'-quotient)**.

`N ⊴ G` で `p ∤ |N|`, `P` が `G` の非自明 `p`-部分群とすると, `f := mk' N` について
`N_Ḡ(P.map f) = (N_G(P)).map f`.

書籍 p.61 の Frattini 議論 (`Sylow.normalizer_sup_eq_top` を `(P ⊔ N).subgroupOf M ⊴ ↥M` に適用). -/
theorem _root_.solution [Finite G] {N : Subgroup G} [N.Normal] {p : ℕ}
    [Fact p.Prime] (hp_coprime : ¬ p ∣ Nat.card N)
    {P : Subgroup G} (hP_pgroup : IsPGroup p P) :
    Subgroup.normalizer ((P.map (QuotientGroup.mk' N)) : Subgroup (G ⧸ N))
      = (Subgroup.normalizer P).map (QuotientGroup.mk' N) := by
  classical
  set f : G →* G ⧸ N := QuotientGroup.mk' N with hf_def
  have hf_surj : Function.Surjective f := QuotientGroup.mk'_surjective N
  have hf_ker : f.ker = N := QuotientGroup.ker_mk' N
  -- Step 1: P ⊓ N = ⊥ (coprimality).
  obtain ⟨k, hP_card⟩ : ∃ k, Nat.card ↥P = p ^ k := IsPGroup.iff_card.mp hP_pgroup
  have hp_prime : p.Prime := Fact.out
  have h_coprime_PN : Nat.Coprime (Nat.card ↥P) (Nat.card ↥N) := by
    rw [hP_card]
    exact Nat.Coprime.pow_left _ (hp_prime.coprime_iff_not_dvd.mpr hp_coprime)
  have hP_inf_N : P ⊓ N = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard h_coprime_PN).eq_bot
  -- Names.
  set Pbar : Subgroup (G ⧸ N) := P.map f with hPbar_def
  set Mbar : Subgroup (G ⧸ N) := Subgroup.normalizer (Pbar : Subgroup (G ⧸ N)) with hMbar_def
  set M : Subgroup G := Mbar.comap f with hM_def
  set L : Subgroup G := Subgroup.normalizer P with hL_def
  set U : Subgroup G := P ⊔ N with hU_def
  -- Step 2: M.map f = Mbar (surjectivity).
  have hM_map : M.map f = Mbar :=
    Subgroup.map_comap_eq_self_of_surjective hf_surj _
  -- Step 3: M = N_G(U) where U = P ⊔ N.
  have hPbar_comap : Pbar.comap f = U := by
    rw [hPbar_def, hU_def, hf_def, QuotientGroup.comap_map_mk' N P, sup_comm]
  have hM_eq_norm_U : M = Subgroup.normalizer U := by
    rw [hM_def, hMbar_def]
    rw [Subgroup.comap_normalizer_eq_of_surjective _ hf_surj, hPbar_comap]
  -- Step 4: L ⊆ M (i.e., N_G(P) ⊆ M).
  -- This is Part 2: (N_G(P)).map f ⊆ N_Ḡ(P̄), reformulated using map_le_iff_le_comap.
  have hL_le_M : L ≤ M := by
    rw [hM_def, ← Subgroup.map_le_iff_le_comap]
    -- Show (N_G(P)).map f ≤ Mbar = N_Ḡ(P̄).
    rw [hMbar_def, hPbar_def]
    exact Subgroup.le_normalizer_map f
  -- We need to also show: L.map f = Mbar (this is the main goal, restated).
  -- ⊇: Already L.map f ≤ Mbar via the above. Now ⊆ needs Frattini.
  -- The goal: Mbar = L.map f.
  -- Strategy: Mbar = M.map f. Show M ≤ L ⊔ N, then M.map f ≤ (L ⊔ N).map f = L.map f.
  refine le_antisymm ?_ ?_
  · -- Mbar ≤ L.map f: requires the Frattini argument.
    -- Step 5: Set up the Frattini argument.
    -- (1) U.subgroupOf M ⊴ ↥M (since M = normalizer U).
    have hUM_normal : (U.subgroupOf M).Normal := by
      rw [hM_eq_norm_U]; exact Subgroup.normal_in_normalizer
    have hP_le_U : P ≤ U := le_sup_left
    have hN_le_U : N ≤ U := le_sup_right
    have hP_le_L : P ≤ L := by rw [hL_def]; exact Subgroup.le_normalizer
    have hL_le_norm_U : L ≤ Subgroup.normalizer U := by
      -- L normalizes P. L also normalizes N (N ⊴ G). So L normalizes P ⊔ N = U.
      -- This is the same h_preserve trick used in Lemma 2.16.
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      have hx_in_norm : x ∈ Subgroup.normalizer (P : Set G) := hx
      have hx_inv_in_norm : x⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
        Subgroup.inv_mem _ hx
      have h_conj_P : ∀ q ∈ P, x * q * x⁻¹ ∈ P :=
        fun q hq => (Subgroup.mem_normalizer_iff.mp hx_in_norm q).mp hq
      have h_conj_P_inv : ∀ q ∈ P, x⁻¹ * q * (x⁻¹)⁻¹ ∈ P :=
        fun q hq => (Subgroup.mem_normalizer_iff.mp hx_inv_in_norm q).mp hq
      have h_conj_N : ∀ n ∈ N, x * n * x⁻¹ ∈ N := fun n hn =>
        Subgroup.Normal.conj_mem ‹N.Normal› n hn x
      have h_conj_N_inv : ∀ n ∈ N, x⁻¹ * n * (x⁻¹)⁻¹ ∈ N := fun n hn =>
        Subgroup.Normal.conj_mem ‹N.Normal› n hn x⁻¹
      have h_preserve : ∀ (g : G), (∀ q ∈ P, g * q * g⁻¹ ∈ P) →
          (∀ n ∈ N, g * n * g⁻¹ ∈ N) →
          ∀ z ∈ P ⊔ N, g * z * g⁻¹ ∈ P ⊔ N := by
        intro g hgP hgN z hz
        rw [Subgroup.sup_eq_closure] at hz
        induction hz using Subgroup.closure_induction with
        | mem w hw =>
          rcases hw with hwP | hwN
          · exact Subgroup.mem_sup_left (hgP w hwP)
          · exact Subgroup.mem_sup_right (hgN w hwN)
        | one =>
          have h1 : g * 1 * g⁻¹ = 1 := by group
          rw [h1]; exact Subgroup.one_mem _
        | mul a b _ _ ha hb =>
          have h_eq : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
          rw [h_eq]; exact Subgroup.mul_mem _ ha hb
        | inv a _ ha =>
          have h_eq : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
          rw [h_eq]; exact Subgroup.inv_mem _ ha
      intro y
      constructor
      · intro hy
        rw [hU_def] at hy ⊢
        exact h_preserve x h_conj_P h_conj_N y hy
      · intro hy
        rw [hU_def] at hy ⊢
        have h_pre : x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ ∈ P ⊔ N :=
          h_preserve x⁻¹ h_conj_P_inv h_conj_N_inv _ hy
        have h_simp : x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ = y := by group
        rwa [h_simp] at h_pre
    -- (2) P is a Sylow p of U = P ⊔ N.
    -- Plan: |U| = |P| · |N| via second iso (P/(P ⊓ N) ≃ U/N).
    --      Then [U:P] = |N|, which is coprime to p.
    have hU_card_eq : Nat.card ↥U = Nat.card ↥P * Nat.card ↥N := by
      rw [hU_def]
      -- (N.subgroupOf P).index = |P| since P ⊓ N = ⊥ (i.e. N.subgroupOf P = ⊥ in ↥P).
      have hNP_eq_bot : N.subgroupOf P = (⊥ : Subgroup ↥P) := by
        rw [Subgroup.eq_bot_iff_forall]
        intro x hx
        have hx_N : (x : G) ∈ N := hx
        have hx_P : (x : G) ∈ P := x.2
        have hx_inf : (x : G) ∈ P ⊓ N := ⟨hx_P, hx_N⟩
        rw [hP_inf_N, Subgroup.mem_bot] at hx_inf
        exact Subtype.ext hx_inf
      have hP_quot_card : Nat.card (↥P ⧸ N.subgroupOf P) = Nat.card ↥P := by
        rw [hNP_eq_bot]
        exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
      -- Second iso: P/(N ⊓ P) ≃* (P ⊔ N)/(N.subgroupOf (P ⊔ N)).
      have h_iso := QuotientGroup.quotientInfEquivProdNormalQuotient P N
      have h_quot_eq : Nat.card (↥P ⧸ N.subgroupOf P)
          = Nat.card (↥(P ⊔ N) ⧸ N.subgroupOf (P ⊔ N)) :=
        Nat.card_congr h_iso.toEquiv
      have h_index_eq : (N.subgroupOf (P ⊔ N)).index = Nat.card ↥P := by
        rw [Subgroup.index_eq_card, ← h_quot_eq, hP_quot_card]
      -- |U| · |N.subgroupOf U| = ... no, use: |N| * [U:N] = |U|.
      -- N.subgroupOf U has |↥(N.subgroupOf U)| = |N| (since N ≤ U).
      have hN_subU_card : Nat.card ↥(N.subgroupOf (P ⊔ N)) = Nat.card ↥N := by
        rw [show Nat.card ↥(N.subgroupOf (P ⊔ N)) =
          Nat.card ↥((N.subgroupOf (P ⊔ N)).map (P ⊔ N).subtype) from
          (Subgroup.card_subtype _ _).symm]
        rw [Subgroup.map_subgroupOf_eq_of_le hN_le_U]
      have h_mul : Nat.card ↥(N.subgroupOf (P ⊔ N)) * (N.subgroupOf (P ⊔ N)).index =
          Nat.card ↥(P ⊔ N) := Subgroup.card_mul_index _
      rw [hN_subU_card, h_index_eq] at h_mul
      linarith
    have hP_subU_index : (P.subgroupOf U).index = Nat.card ↥N := by
      have h_mul : Nat.card ↥(P.subgroupOf U) * (P.subgroupOf U).index = Nat.card ↥U :=
        Subgroup.card_mul_index _
      have hP_subU_card : Nat.card ↥(P.subgroupOf U) = Nat.card ↥P := by
        rw [show Nat.card ↥(P.subgroupOf U) =
          Nat.card ↥((P.subgroupOf U).map U.subtype) from
          (Subgroup.card_subtype _ _).symm]
        rw [Subgroup.map_subgroupOf_eq_of_le hP_le_U]
      rw [hP_subU_card, hU_card_eq] at h_mul
      have hP_pos : 0 < Nat.card ↥P := Nat.card_pos
      have hN_pos : 0 < Nat.card ↥N := Nat.card_pos
      -- |P| * idx = |P| * |N|, so idx = |N|.
      exact Nat.eq_of_mul_eq_mul_left hP_pos h_mul
    have hP_subU_not_dvd : ¬ p ∣ (P.subgroupOf U).index := by
      rw [hP_subU_index]; exact hp_coprime
    -- P.subgroupOf U is a p-group (since it is isomorphic to P).
    have : Finite ↥U := Subtype.finite
    have hP_subU_pgroup : IsPGroup p ↥(P.subgroupOf U) :=
      hP_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hP_le_U).symm
    let PS : Sylow p ↥U := hP_subU_pgroup.toSylow hP_subU_not_dvd
    have hPS_eq : (PS : Subgroup ↥U) = P.subgroupOf U :=
      hP_subU_pgroup.toSylow_coe hP_subU_not_dvd
    -- (3) Build P_M : Sylow p ↥(U.subgroupOf M) using e := subgroupOfEquivOfLe hU_le_M.
    have hU_le_M : U ≤ M := by rw [hM_eq_norm_U]; exact Subgroup.le_normalizer
    have : Finite ↥M := Subtype.finite
    have : Finite ↥(U.subgroupOf M) := Subtype.finite
    let e : ↥(U.subgroupOf M) ≃* ↥U := Subgroup.subgroupOfEquivOfLe hU_le_M
    let P_M : Sylow p ↥(U.subgroupOf M) :=
      Sylow.ofCard ((PS : Subgroup ↥U).comap e.toMonoidHom) (by
        rw [show Nat.card ↥(U.subgroupOf M) = Nat.card ↥U from Nat.card_congr e.toEquiv]
        have h_card_eq : Nat.card ↥((PS : Subgroup ↥U).comap e.toMonoidHom) =
            Nat.card (PS : Subgroup ↥U) := by
          refine Nat.card_congr ?_
          exact {
            toFun := fun x => ⟨e x.1, x.2⟩
            invFun := fun y => ⟨e.symm y.1, by
              change e (e.symm y.1) ∈ (PS : Subgroup ↥U)
              rw [MulEquiv.apply_symm_apply]
              exact y.2⟩
            left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
            right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1)
          }
        rw [h_card_eq, Sylow.card_eq_multiplicity PS])
    -- (4) Apply Sylow.normalizer_sup_eq_top.
    have h_frattini : Subgroup.normalizer (P_M.map (U.subgroupOf M).subtype) ⊔
        U.subgroupOf M = ⊤ :=
      Sylow.normalizer_sup_eq_top P_M
    -- (5) Identify (P_M.map (U.subgroupOf M).subtype).map M.subtype = P.
    have h_PM_map_eq : ((P_M.map (U.subgroupOf M).subtype : Subgroup ↥M).map M.subtype) = P := by
      ext y
      simp only [Subgroup.mem_map, Subgroup.coe_subtype]
      constructor
      · rintro ⟨a, ⟨b, hb, hba⟩, hay⟩
        have hb' : e b ∈ (PS : Subgroup ↥U) := by
          change b ∈ (PS : Subgroup ↥U).comap e.toMonoidHom at hb
          rw [Subgroup.mem_comap] at hb; exact hb
        rw [hPS_eq] at hb'
        -- e b : ↥U, (e b : G) = b.val.val. We want y ∈ P.
        have he_val : ((e b : ↥U) : G) = ((b : ↥(U.subgroupOf M)) : ↥M).1 := rfl
        have hb_subOf : (e b : G) ∈ P := hb'
        have : ((b : ↥(U.subgroupOf M)) : ↥M).1 = (e b : G) := he_val.symm
        rw [← hay, ← hba]
        change ((b : ↥(U.subgroupOf M)) : ↥M).1 ∈ P
        rw [this]; exact hb_subOf
      · rintro hzP
        refine ⟨⟨y, hU_le_M (hP_le_U hzP)⟩, ⟨e.symm ⟨y, hP_le_U hzP⟩, ?_, ?_⟩, rfl⟩
        · change e.symm ⟨y, hP_le_U hzP⟩ ∈ (PS : Subgroup ↥U).comap e.toMonoidHom
          rw [Subgroup.mem_comap]
          simp only [MulEquiv.apply_symm_apply, MulEquiv.coe_toMonoidHom]
          rw [hPS_eq]
          exact hzP
        · rfl
    -- (6) Frattini in G: each m ∈ M decomposes as m = a * b with a ∈ L = N_G(P), b ∈ U.
    have hM_le_L_sup_U : M ≤ L ⊔ U := by
      intro m hm
      have hm_M : (⟨m, hm⟩ : ↥M) ∈ (⊤ : Subgroup ↥M) := trivial
      rw [← h_frattini] at hm_M
      rcases Subgroup.mem_sup_of_normal_right.mp hm_M with ⟨a, ha, b, hb, hab⟩
      have hMb_U : (b : G) ∈ U := by
        change b ∈ U.subgroupOf M at hb
        exact hb
      have hMa_L : (a : G) ∈ L := by
        rw [hL_def, Subgroup.mem_normalizer_iff]
        intro y
        have ha_norm : a ∈ Subgroup.normalizer (P_M.map (U.subgroupOf M).subtype) := ha
        rw [Subgroup.mem_normalizer_iff] at ha_norm
        constructor
        · intro hy
          have hy_U : y ∈ U := hP_le_U hy
          have hy_M : y ∈ M := hU_le_M hy_U
          have hy_PM_map : (⟨y, hy_M⟩ : ↥M) ∈ P_M.map (U.subgroupOf M).subtype := by
            rw [← h_PM_map_eq] at hy
            rcases Subgroup.mem_map.mp hy with ⟨x, hx, hxy⟩
            have hx_eq : x = ⟨y, hy_M⟩ := Subtype.ext hxy
            rw [hx_eq] at hx; exact hx
          have h_step := (ha_norm ⟨y, hy_M⟩).mp hy_PM_map
          have h_step_G : (a : G) * y * (a : G)⁻¹ ∈ P := by
            rw [← h_PM_map_eq]
            refine ⟨a * ⟨y, hy_M⟩ * a⁻¹, h_step, ?_⟩
            rfl
          exact h_step_G
        · intro hy
          have ha_inv_norm : a⁻¹ ∈ Subgroup.normalizer (P_M.map (U.subgroupOf M).subtype) :=
            (Subgroup.normalizer _).inv_mem ha
          rw [Subgroup.mem_normalizer_iff] at ha_inv_norm
          have hay_U : (a : G) * y * (a : G)⁻¹ ∈ U := hP_le_U hy
          have hy_M : y ∈ M := by
            have : (a : G)⁻¹ * ((a : G) * y * (a : G)⁻¹) * ((a : G)⁻¹)⁻¹ = y := by group
            rw [← this]
            exact M.mul_mem (M.mul_mem (M.inv_mem a.2) (hU_le_M hay_U)) (M.inv_mem (M.inv_mem a.2))
          have hay_PM_map : (⟨(a : G) * y * (a : G)⁻¹, hU_le_M hay_U⟩ : ↥M)
              ∈ P_M.map (U.subgroupOf M).subtype := by
            rw [← h_PM_map_eq] at hy
            rcases Subgroup.mem_map.mp hy with ⟨x, hx, hxy⟩
            have hx_eq : x = ⟨(a : G) * y * (a : G)⁻¹, hU_le_M hay_U⟩ := Subtype.ext hxy
            rw [hx_eq] at hx; exact hx
          have h_back := (ha_inv_norm ⟨(a : G) * y * (a : G)⁻¹, hU_le_M hay_U⟩).mp hay_PM_map
          have h_back_G : (a : G)⁻¹ * ((a : G) * y * (a : G)⁻¹) * ((a : G)⁻¹)⁻¹ ∈ P := by
            rw [← h_PM_map_eq]
            refine ⟨a⁻¹ * ⟨(a : G) * y * (a : G)⁻¹, hU_le_M hay_U⟩ * (a⁻¹)⁻¹, h_back, ?_⟩
            rfl
          have h_simp : (a : G)⁻¹ * ((a : G) * y * (a : G)⁻¹) * ((a : G)⁻¹)⁻¹ = y := by group
          rwa [h_simp] at h_back_G
      have hm_eq : m = (a : G) * (b : G) := by
        have h := congrArg ((↑) : ↥M → G) hab
        simp at h; exact h.symm
      rw [hm_eq]
      exact (L ⊔ U).mul_mem (Subgroup.mem_sup_left hMa_L) (Subgroup.mem_sup_right hMb_U)
    -- (7) Now M ⊆ L ⊔ U. Map to quotient: Mbar ⊆ (L ⊔ U).map f.
    -- (L ⊔ U).map f = L.map f ⊔ U.map f = L.map f ⊔ (P ⊔ N).map f
    --              = L.map f ⊔ P.map f ⊔ N.map f
    --              = L.map f ⊔ Pbar ⊔ ⊥ = L.map f (since P ≤ L ⇒ Pbar ≤ L.map f).
    rw [← hM_map]
    have h_step1 : M.map f ≤ (L ⊔ U).map f := Subgroup.map_mono hM_le_L_sup_U
    have h_N_map : N.map f = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      rcases hx with ⟨y, hy, hyx⟩
      rw [Subgroup.mem_bot]
      rw [← hyx]
      have : y ∈ f.ker := by rw [hf_ker]; exact hy
      exact this
    have h_step2 : (L ⊔ U).map f = L.map f := by
      rw [hU_def, ← sup_assoc, Subgroup.map_sup, Subgroup.map_sup]
      have h_P_le_L_map : P.map f ≤ L.map f := Subgroup.map_mono hP_le_L
      rw [h_N_map, sup_bot_eq]
      exact sup_eq_left.mpr h_P_le_L_map
    rw [← h_step2]
    exact h_step1
  · -- L.map f ≤ Mbar: this is Part 2.
    rw [hMbar_def, hPbar_def]
    exact Subgroup.le_normalizer_map f

end

end OddOrder.Isaacs.Ch02

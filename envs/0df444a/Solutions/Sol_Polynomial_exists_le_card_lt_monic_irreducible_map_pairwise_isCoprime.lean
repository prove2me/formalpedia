-- Prove2me | solution 1 for Polynomial.exists_le_card_lt_monic_irreducible_map_pairwise_isCoprime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c0afecf2-5fc5-57ca-b641-c759a760e8d3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_exists_le_card_lt_monic_irreducible_map_pairwise_isCoprime

set_option autoImplicit false

open Polynomial IntermediateField

noncomputable section

namespace CCOUNT

theorem sum_pow_le (ℓ m : ℕ) (hℓ : 2 ≤ ℓ) : ∑ d ∈ Finset.range (m + 1), ℓ ^ d ≤ ℓ ^ (m + 1) := by
  induction m with
  | zero => simp; omega
  | succ m ih =>
    rw [Finset.sum_range_succ]
    calc ∑ d ∈ Finset.range (m + 1), ℓ ^ d + ℓ ^ (m + 1) ≤ ℓ ^ (m + 1) + ℓ ^ (m + 1) := by omega
      _ = 2 * ℓ ^ (m + 1) := by ring
      _ ≤ ℓ * ℓ ^ (m + 1) := Nat.mul_le_mul_right _ hℓ
      _ = ℓ ^ (m + 1 + 1) := by ring

theorem exists_finset_monic_irreducible (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (D : ℕ) (hD : 1 ≤ D) :
    ∃ S : Finset (Polynomial (ZMod ℓ)),
      (∀ f ∈ S, f.Monic ∧ f.natDegree = D ∧ Irreducible f) ∧
      ℓ ^ D ≤ D * S.card + ℓ ^ (D / 2 + 1) := by
  classical
  have hD0 : D ≠ 0 := by omega
  let K := GaloisField ℓ D
  haveI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = ℓ ^ D := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card ℓ D hD0
  have hfin : Module.finrank (ZMod ℓ) K = D := GaloisField.finrank ℓ hD0
  have hint : ∀ α : K, IsIntegral (ZMod ℓ) α := fun α => Algebra.IsIntegral.isIntegral α

  let gen : Finset K := Finset.univ.filter fun α => (minpoly (ZMod ℓ) α).natDegree = D
  let S : Finset (Polynomial (ZMod ℓ)) := gen.image (minpoly (ZMod ℓ))
  refine ⟨S, ?_, ?_⟩
  · intro f hf
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hf
    exact ⟨minpoly.monic (hint α), (Finset.mem_filter.mp hα).2, minpoly.irreducible (hint α)⟩
  ·
    have hfib : gen.card ≤ D * S.card := by
      refine Finset.card_le_mul_card_image _ D (fun f hf => ?_)
      obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hf
      have hdeg : (minpoly (ZMod ℓ) α).natDegree = D := (Finset.mem_filter.mp hα).2

      calc (gen.filter fun a => minpoly (ZMod ℓ) a = minpoly (ZMod ℓ) α).card
          ≤ ((minpoly (ZMod ℓ) α).map (algebraMap (ZMod ℓ) K)).roots.toFinset.card := by
            apply Finset.card_le_card
            intro β hβ
            have hβ' : minpoly (ZMod ℓ) β = minpoly (ZMod ℓ) α := (Finset.mem_filter.mp hβ).2
            rw [Multiset.mem_toFinset, mem_roots ((minpoly.monic (hint α)).map _).ne_zero, IsRoot, eval_map,
              ← aeval_def, ← hβ']
            exact minpoly.aeval _ _
        _ ≤ ((minpoly (ZMod ℓ) α).map (algebraMap (ZMod ℓ) K)).roots.card := Multiset.toFinset_card_le _
        _ ≤ ((minpoly (ZMod ℓ) α).map (algebraMap (ZMod ℓ) K)).natDegree := card_roots' _
        _ = D := by rw [(minpoly.monic (hint α)).natDegree_map, hdeg]

    have hnongen : (Finset.univ.filter fun α : K => (minpoly (ZMod ℓ) α).natDegree ≠ D).card ≤
        ∑ d ∈ Finset.range (D / 2 + 1), ℓ ^ d := by

      let R : ℕ → Finset K := fun d => ((X ^ ℓ ^ d - X : Polynomial K)).roots.toFinset
      have hRcard : ∀ d, (R d).card ≤ ℓ ^ d := by
        intro d
        rcases Nat.eq_zero_or_pos d with rfl | hd
        ·
          simp [R]
        · have h1 : 1 < ℓ ^ d := Nat.one_lt_pow hd.ne' hℓ.out.one_lt
          calc (R d).card ≤ (X ^ ℓ ^ d - X : Polynomial K).roots.card := Multiset.toFinset_card_le _
            _ ≤ (X ^ ℓ ^ d - X : Polynomial K).natDegree := card_roots' _
            _ = ℓ ^ d := FiniteField.X_pow_card_sub_X_natDegree_eq K h1
      have hsub : (Finset.univ.filter fun α : K => (minpoly (ZMod ℓ) α).natDegree ≠ D) ⊆
          (Finset.range (D / 2 + 1)).biUnion R := by
        intro α hα
        have hne : (minpoly (ZMod ℓ) α).natDegree ≠ D := (Finset.mem_filter.mp hα).2
        set d := (minpoly (ZMod ℓ) α).natDegree with hd

        have hdvd : d ∣ D := by
          have h1 : Module.finrank (ZMod ℓ) (ZMod ℓ)⟮α⟯ = d := IntermediateField.adjoin.finrank (hint α)
          have h2 := Module.finrank_mul_finrank (ZMod ℓ) (ZMod ℓ)⟮α⟯ K
          rw [h1, hfin] at h2
          exact Dvd.intro _ h2
        have hle : d ≤ D := by
          have := minpoly.natDegree_le (A := ZMod ℓ) α
          rwa [hfin] at this
        have hdpos : 0 < d := (minpoly.natDegree_pos (hint α))
        have hd2 : d ≤ D / 2 := by
          obtain ⟨k, hk⟩ := hdvd
          have hk2 : 2 ≤ k := by
            by_contra hk2
            push Not at hk2
            interval_cases k
            · simp at hk; omega
            · rw [mul_one] at hk; exact hne hk.symm
          rw [Nat.le_div_iff_mul_le (by norm_num)]
          calc d * 2 ≤ d * k := Nat.mul_le_mul_left d hk2
            _ = D := hk.symm

        have hpow : α ^ ℓ ^ d = α := by
          let L := (ZMod ℓ)⟮α⟯
          haveI : Fintype L := Fintype.ofFinite L
          have hcardL : Fintype.card L = ℓ ^ d := by
            rw [Module.card_eq_pow_finrank (K := ZMod ℓ) (V := L), ZMod.card, IntermediateField.adjoin.finrank (hint α)]
          have a_mem : α ∈ L := IntermediateField.mem_adjoin_simple_self (ZMod ℓ) α
          have := FiniteField.pow_card (⟨α, a_mem⟩ : L)
          rw [hcardL] at this
          exact congrArg Subtype.val this
        refine Finset.mem_biUnion.mpr ⟨d, Finset.mem_range.mpr (by omega), ?_⟩
        have h1 : 1 < ℓ ^ d := Nat.one_lt_pow hdpos.ne' hℓ.out.one_lt
        rw [Multiset.mem_toFinset, mem_roots (FiniteField.X_pow_card_sub_X_ne_zero K h1), IsRoot]
        simp [hpow]
      calc (Finset.univ.filter fun α : K => (minpoly (ZMod ℓ) α).natDegree ≠ D).card
          ≤ ((Finset.range (D / 2 + 1)).biUnion R).card := Finset.card_le_card hsub
        _ ≤ ∑ d ∈ Finset.range (D / 2 + 1), (R d).card := Finset.card_biUnion_le
        _ ≤ ∑ d ∈ Finset.range (D / 2 + 1), ℓ ^ d := Finset.sum_le_sum fun d _ => hRcard d

    have hsplit : Fintype.card K =
        gen.card + (Finset.univ.filter fun α : K => (minpoly (ZMod ℓ) α).natDegree ≠ D).card := by
      rw [← Finset.card_univ]
      exact (Finset.card_filter_add_card_filter_not _).symm
    have := sum_pow_le ℓ (D / 2) hℓ.out.two_le
    omega

theorem exists_mul_pow_lt_two_pow (k C N₀ : ℕ) : ∃ D : ℕ, N₀ ≤ D ∧ C * D ^ k < 2 ^ D := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt k (one_lt_two : (1 : ℝ) < 2)
  have hev : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ k / 2 ^ n < 1 / (C + 1) :=
    ht.eventually (gt_mem_nhds (by positivity))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨m, hmN, hmN₀⟩ : ∃ m : ℕ, N ≤ m ∧ N₀ ≤ m := ⟨max N N₀, le_max_left _ _, le_max_right _ _⟩
  refine ⟨m, hmN₀, ?_⟩
  have h := hN m hmN
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  rw [div_lt_div_iff₀ h2 (by positivity : (0 : ℝ) < C + 1), one_mul] at h
  have hmk : (0 : ℝ) ≤ (m : ℝ) ^ k := by positivity
  have h' : ((C * m ^ k : ℕ) : ℝ) < ((2 ^ m : ℕ) : ℝ) := by
    push_cast
    calc (C : ℝ) * (m : ℝ) ^ k ≤ (m : ℝ) ^ k * (C + 1) := by nlinarith [hmk]
      _ < 2 ^ m := h
  exact_mod_cast h'

end CCOUNT

open CCOUNT in
theorem solution
    (ℓ : ℕ) [Fact ℓ.Prime] (n₀ A₀ B₀ c N₀ : ℕ)
    (avoid : Polynomial (ZMod ℓ)) (havoid : avoid ≠ 0) :
    ∃ (D M : ℕ) (g : Fin M → Polynomial ℤ),
      2 ≤ D ∧ N₀ ≤ D ∧ A₀ * (c * D) ^ n₀ + B₀ < M ∧
      (∀ i, (g i).Monic ∧ (g i).natDegree = D) ∧
      (∀ i, Irreducible ((g i).map (Int.castRingHom (ZMod ℓ)))) ∧
      (∀ i, ((g i).map (Int.castRingHom (ZMod ℓ))).Separable) ∧
      (∀ i j, i ≠ j →
        IsCoprime ((g i).map (Int.castRingHom (ZMod ℓ))) ((g j).map (Int.castRingHom (ZMod ℓ)))) ∧
      (∀ i, IsCoprime ((g i).map (Int.castRingHom (ZMod ℓ))) avoid) ∧
      (∀ i, ((g i).map (Int.castRingHom (ZMod ℓ))).eval 0 ≠ 0) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have hℓ2 : 2 ≤ ℓ := hℓ.two_le

  set Cst : ℕ := 2 * (A₀ * c ^ n₀ + B₀ + 1) with hCst
  obtain ⟨D, hDN, hDlt⟩ := exists_mul_pow_lt_two_pow (n₀ + 1) Cst (max (max 4 (avoid.natDegree + 1)) N₀)
  have hD4 : 4 ≤ D := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hDN)
  have hDav : avoid.natDegree < D := lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hDN))
  have hDN₀ : N₀ ≤ D := le_trans (le_max_right _ _) hDN

  obtain ⟨S, hS, hcount⟩ := exists_finset_monic_irreducible ℓ D (by omega)

  have hbig : A₀ * (c * D) ^ n₀ + B₀ < S.card := by

    have hhalf : 2 * ℓ ^ (D / 2 + 1) ≤ ℓ ^ D := by
      calc 2 * ℓ ^ (D / 2 + 1) ≤ ℓ * ℓ ^ (D / 2 + 1) := Nat.mul_le_mul_right _ hℓ2
        _ = ℓ ^ (D / 2 + 2) := by ring
        _ ≤ ℓ ^ D := Nat.pow_le_pow_right (by omega) (by omega)
    have h2D : 2 ^ D ≤ ℓ ^ D := Nat.pow_le_pow_left hℓ2 D

    have hpoly : 2 * (D * (A₀ * (c * D) ^ n₀ + B₀ + 1)) ≤ Cst * D ^ (n₀ + 1) := by
      rw [hCst, mul_pow, pow_succ]
      have hD1 : 1 ≤ D ^ n₀ := Nat.one_le_pow _ _ (by omega)
      have e1 : D * B₀ * 1 ≤ D * B₀ * D ^ n₀ := Nat.mul_le_mul_left _ hD1
      have e2 : D * 1 ≤ D * D ^ n₀ := Nat.mul_le_mul_left _ hD1
      nlinarith [e1, e2]

    nlinarith [hcount, hhalf, h2D, hpoly, hDlt]

  set M := S.card with hM
  let e : Fin M → Polynomial (ZMod ℓ) := fun i => (S.equivFin.symm i).1
  have he_mem : ∀ i, e i ∈ S := fun i => (S.equivFin.symm i).2
  have he_inj : Function.Injective e := fun i j h =>
    S.equivFin.symm.injective (Subtype.ext h)
  have hsurj : Function.Surjective (Int.castRingHom (ZMod ℓ)) := ZMod.intCast_surjective
  have hlift : ∀ i, ∃ q : Polynomial ℤ, q.map (Int.castRingHom (ZMod ℓ)) = e i ∧ q.natDegree = D ∧ q.Monic := by
    intro i
    obtain ⟨hmon, hdeg, -⟩ := hS _ (he_mem i)
    obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic
      ((mem_lifts _).mpr (map_surjective _ hsurj _)) hmon
    exact ⟨q, hq, hqd.trans hdeg, hqm⟩
  choose g hg_map hg_deg hg_mon using hlift
  haveI : Fact ℓ.Prime := ‹_›
  refine ⟨D, M, g, by omega, hDN₀, hbig, fun i => ⟨hg_mon i, hg_deg i⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; rw [hg_map]; exact (hS _ (he_mem i)).2.2
  · intro i; rw [hg_map]; exact PerfectField.separable_of_irreducible (hS _ (he_mem i)).2.2
  · intro i j hij
    rw [hg_map, hg_map]
    obtain ⟨hmi, hdi, hirri⟩ := hS _ (he_mem i)
    obtain ⟨hmj, hdj, hirrj⟩ := hS _ (he_mem j)
    refine (hirri.coprime_iff_not_dvd).mpr fun hdvd => hij (he_inj ?_)
    exact eq_of_monic_of_associated hmi hmj (hirri.associated_of_dvd hirrj hdvd)
  · intro i
    rw [hg_map]
    obtain ⟨hmi, hdi, hirri⟩ := hS _ (he_mem i)
    refine (hirri.coprime_iff_not_dvd).mpr fun hdvd => ?_
    have := natDegree_le_of_dvd hdvd havoid
    omega
  · intro i h0
    rw [hg_map] at h0
    obtain ⟨hmi, hdi, hirri⟩ := hS _ (he_mem i)
    have hX : (X : Polynomial (ZMod ℓ)) ∣ e i := by
      rw [← sub_zero X, ← C_0, dvd_iff_isRoot]; exact h0
    have hass := irreducible_X.associated_of_dvd hirri hX
    have := natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hass)
    rw [natDegree_X, hdi] at this
    omega

end

end S_Polynomial_exists_le_card_lt_monic_irreducible_map_pairwise_isCoprime
end P2MW
export P2MW.S_Polynomial_exists_le_card_lt_monic_irreducible_map_pairwise_isCoprime (solution)

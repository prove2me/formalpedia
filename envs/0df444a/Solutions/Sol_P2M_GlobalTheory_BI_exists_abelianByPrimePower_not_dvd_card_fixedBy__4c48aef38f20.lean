-- Prove2me | solution 1 for P2M_GlobalTheory_BI_exists_abelianByPrimePower_not_dvd_card_fixedBy__4c48aef38f20
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:43:46.483861+00:00
-- url     : https://prove2.me/submissions/f0257450-9095-4c0e-9a47-17447a192e53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardFixedByQuotientEqRelIndexOfPRegularStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardFixedByPowPrimePowModEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsCoprimeOrderOfPowPrimePowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsSylowOverSubgroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsAbelianByPrimePowerNotDvdCardFixedBy
import Theorems.Thm_GlobalTheory_T_card_fixedBy_pow_prime_pow_modEq_card_fixedBy
import Theorems.Thm_GlobalTheory_T_card_fixedBy_quotient_eq_relIndex_normalizer_of_coprime
import Theorems.Thm_GlobalTheory_T_exists_subgroup_ge_normalizing_not_dvd_relIndex
import Theorems.Thm_P2M_GlobalTheory_T_exists_coprime_orderOf_pow_prime_pow__cf23029f3352


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
open GlobalTheory GlobalTheory.BI
namespace GlobalTheory.BI
theorem _root_.solution :
    ∀ (G : Type) [Group G] [Finite G] (x : G) (p : ℕ), p.Prime →
      ∃ H : Subgroup G, AbByP H ∧ ¬ p ∣ Nat.card (MulAction.fixedBy (G ⧸ H) x) := by
  intro G _ _ x p hp
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_coprime_orderOf_pow_prime_pow' G x p hp
  obtain ⟨H, hCH, hnorm, hpow, hidx⟩ := GlobalTheory.T.exists_subgroup_ge_normalizing_not_dvd_relIndex G (Subgroup.zpowers (x ^ p ^ k)) p hp
  have hN : ∀ g : G, g ∈ Subgroup.normalizer ((Subgroup.zpowers (x ^ p ^ k) : Subgroup G) : Set G) ↔
      ∀ d ∈ Subgroup.zpowers (x ^ p ^ k), g * d * g⁻¹ ∈ Subgroup.zpowers (x ^ p ^ k) := by
    intro g
    constructor
    · intro hg d hd
      exact (Subgroup.mem_normalizer_iff.1 hg d).1 hd
    · intro h
      exact Subgroup.mem_normalizer_fintype h
  refine ⟨H, ⟨p, hp, (Subgroup.zpowers (x ^ p ^ k)).subgroupOf H, ⟨?_⟩, ?_, ?_⟩, ?_⟩
  · intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm g g.2 n hn
  · intro a ha b hb
    rw [Subgroup.mem_subgroupOf] at ha hb
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hm, ← hn]
    exact (Commute.refl _).zpow_zpow m n
  · intro g
    obtain ⟨j, hj⟩ := hpow g g.2
    exact ⟨j, by rw [Subgroup.mem_subgroupOf]; simpa using hj⟩
  · intro hd
    haveI : Finite (G ⧸ H) := inferInstance
    have h1 := GlobalTheory.T.card_fixedBy_quotient_eq_relIndex_normalizer_of_coprime G (x ^ p ^ k) p H _ hk hCH hpow hN
    have h2 := GlobalTheory.T.card_fixedBy_pow_prime_pow_modEq_card_fixedBy G (G ⧸ H) x p k hp
    apply hidx _ hN
    rw [← h1]
    exact (h2.dvd_iff dvd_rfl).2 hd
end GlobalTheory.BI

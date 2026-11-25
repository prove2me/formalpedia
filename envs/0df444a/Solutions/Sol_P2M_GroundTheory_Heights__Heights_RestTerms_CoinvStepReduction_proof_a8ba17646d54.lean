-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CoinvStepReduction_proof_a8ba17646d54
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:41:58.154066+00:00
-- url     : https://prove2.me/submissions/e7ac0820-ee73-4143-832a-5de583115039

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvStepReduction
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_exists_reduction_02442a102c9c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open Coinv
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace CoinvStepReduction
theorem _root_.solution : CoinvStepReduction.Statement := by
  classical
  intro K _ _ f n b k e he
  obtain ⟨c, hc⟩ := Coinv.exists_reduction (K := K) (f := f) (n := n) b k
  set φ : ↥(Finset.Ioi k) → Fin f × Fin n := fun s => (b, (s : Fin n)) with hφ
  have hinj : Function.Injective φ := fun s t h => Subtype.ext (Prod.ext_iff.mp h).2
  obtain ⟨e₀, rfl⟩ : ∃ e₀ : Fin f × Fin n →₀ ℕ, e = e₀ + Finsupp.single (b, k) ((k : ℕ) + 1) := by
    refine ⟨e - Finsupp.single (b, k) ((k : ℕ) + 1), ?_⟩
    ext u
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
    by_cases hu : u = (b, k)
    · subst hu; simp only [Finsupp.single_eq_same]; omega
    · simp [Ne.symm hu]
  set P : MvPolynomial (Fin f × Fin n) K := ∑ j ∈ range ((k : ℕ) + 1),
      monomial e₀ 1 * (rename φ (-c j) * X (b, k) ^ j) with hP
  refine ⟨P.support, fun e' => P.coeff e', ?_, ?_⟩
  · intro e' he'
    have h1 := support_sum he'
    rw [Finset.mem_biUnion] at h1
    obtain ⟨j, hj, hj'⟩ := h1
    have h2 := support_mul _ _ hj'
    rw [Finset.mem_add] at h2
    obtain ⟨a, ha, d', hd', rfl⟩ := h2
    have ha' : a = e₀ := Finset.mem_singleton.mp (support_monomial_subset ha)
    have h3 := support_mul _ _ hd'
    rw [Finset.mem_add] at h3
    obtain ⟨d, hd, s, hs, rfl⟩ := h3
    rw [X_pow_eq_monomial] at hs
    have hs' : s = Finsupp.single (b, k) j := Finset.mem_singleton.mp (support_monomial_subset hs)
    rw [support_rename_of_injective hinj, Finset.mem_image] at hd
    obtain ⟨d₀, -, rfl⟩ := hd
    subst ha' hs'
    have hoff : ∀ u : Fin f × Fin n, (u.1 ≠ b ∨ u.2 ≤ k) → Finsupp.mapDomain φ d₀ u = 0 := by
      intro u hu
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨s, rfl⟩
      have hks : k < (s : Fin n) := Finset.mem_Ioi.mp s.2
      rcases hu with hu | hu
      · exact hu rfl
      · exact absurd hu (not_le.mpr hks)
    rw [Finset.mem_range] at hj
    refine ⟨fun u hu => ?_, ?_⟩
    · have hne : u ≠ (b, k) := by
        rintro rfl
        rcases hu with h | ⟨-, h⟩ <;> exact lt_irrefl _ h
      have h0 := hoff u (by
        rcases hu with h | ⟨-, h⟩
        · exact Or.inl (ne_of_lt h)
        · exact Or.inr (le_of_lt h))
      simp [h0, Ne.symm hne]
    · have h0 := hoff (b, k) (Or.inr le_rfl)
      simp only [Finsupp.add_apply, h0, Finsupp.single_eq_same]
      omega
  · have hsum : ∑ e' ∈ P.support, P.coeff e' • monomial e' (1 : K) = P := by
      conv_rhs => rw [P.as_sum]
      refine Finset.sum_congr rfl fun e' _ => ?_
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hsum]
    have hm : monomial (e₀ + Finsupp.single (b, k) ((k : ℕ) + 1)) (1 : K) =
        monomial e₀ 1 * X (b, k) ^ ((k : ℕ) + 1) := by
      rw [X_pow_eq_monomial, monomial_mul, one_mul]
    have hdiff : monomial (e₀ + Finsupp.single (b, k) ((k : ℕ) + 1)) (1 : K) - P =
        monomial e₀ 1 * (X (b, k) ^ ((k : ℕ) + 1) +
          ∑ j ∈ range ((k : ℕ) + 1), rename φ (c j) * X (b, k) ^ j) := by
      rw [hm, hP, mul_add, Finset.mul_sum]
      simp only [map_neg, neg_mul, mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add]
    rw [hdiff]
    exact Ideal.mul_mem_left _ _ hc
end CoinvStepReduction
end GroundTheory.Heights₂.Heights.RestTerms

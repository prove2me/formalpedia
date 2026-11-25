-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_syzygy_term_zero_de0130de93cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:36.774769+00:00
-- url     : https://prove2.me/submissions/340d78b3-f7b1-4ca9-bc08-6ddcfe096d55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealRootRingToRealAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealTransferOfSyzygy
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_summable_signed_609d30551a2b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_flagIntegral_add_smul_15ff1eab2e68
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_C_43a59c7a9997
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_X_6be993a34174
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_C_43a59c7a9997
attribute [local simp] P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_X_6be993a34174



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.RestBoundEq
namespace GroundTheory.Heights₂.Heights.RestTerms.RestBoundEq
theorem _root_.solution (hA : RestBound.Statement) (f r a : ℕ) (c : SmallBlock)
    (hf : 1 ≤ f) (hr : 1 ≤ r) (ha : 1 ≤ a) (S : ℕ → Fin f → RootRing f (r + a))
    (hS : IsPowerSumDecomposition f (r + a) 0 S) (τ τ' : Fin f) (m : ℕ) (hm2 : 2 ≤ m)
    (hmN : m ≤ r + a) :
    flagIntegral f (r + a) (smallPowerSum f r a c (m - 1) τ' * S m τ) = 0 := by
  set B₀ : ℝ := 4 * (f : ℝ) * ((r + a : ℕ) : ℝ) ^ 2
  obtain ⟨⟨Q₀, hQ₀⟩, hall⟩ := hA f r a c B₀ hf hr ha le_rfl
  obtain ⟨p, hpB, hp⟩ := Nat.exists_infinite_primes (⌈B₀⌉₊ + 1)
  have hBp : B₀ < p := by
    have := Nat.le_ceil B₀
    have h2 : ((⌈B₀⌉₊ + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast hpB
    push_cast at h2
    linarith
  have hp2 : 2 ≤ p := hp.two_le
  set Bnd : ℝ := 1.6 * ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)|

  set Qt : ℚ → ℕ → Fin f → RootRing f (r + a) := fun t k σ => Q₀ k σ + t • S k σ with hQt
  have hQtd : ∀ t, IsPowerSumDecomposition f (r + a) (restPolynomial f r a c) (Qt t) := by
    intro t
    unfold IsPowerSumDecomposition at hQ₀ hS ⊢
    simp only [hQt, mul_add, mul_smul_comm, sum_add_distrib, ← smul_sum, ← hS, smul_zero,
      add_zero]
    exact hQ₀
  set s : ℕ → ℕ → Fin f → Fin f := fun _ _ _ => τ'
  set e₁ : ℕ → ℕ → Fin f → ℕ → ℚ := fun _ _ _ _ => 1
  set e₂ : ℕ → ℕ → Fin f → ℕ → ℚ := fun _ n σ k => if n = 1 ∧ σ = τ ∧ k = m then -1 else 1
  have he₁ : ∀ q n σ k, e₁ q n σ k = 1 ∨ e₁ q n σ k = -1 := fun _ _ _ _ => Or.inl rfl
  have he₂ : ∀ q n σ k, e₂ q n σ k = 1 ∨ e₂ q n σ k = -1 := fun _ n σ k => by
    simp only [e₂]; split_ifs <;> simp

  have hone : ∀ g : ℕ → ℝ,
      ∑' q : {q : ℕ // q ∈ ({p} : Set ℕ) ∧ q.Prime ∧ B₀ < q}, g q = g p := by
    intro g
    rw [tsum_eq_single (⟨p, rfl, hp, hBp⟩ : {q : ℕ // q ∈ ({p} : Set ℕ) ∧ q.Prime ∧ B₀ < q})
      (fun b hb => absurd (Subtype.ext (Set.mem_singleton_iff.1 b.2.1)) hb)]
  have hbd : ∀ t (e : ℕ → ℕ → Fin f → ℕ → ℚ), (∀ q n σ k, e q n σ k = 1 ∨ e q n σ k = -1) →
      |restPrimeModel f r a c (Qt t) s e p| ≤ Bnd := by
    intro t e he
    have := (hall (Qt t) (hQtd t) s e he {p}).2
    rwa [hone] at this

  have hdiff : ∀ Q : ℕ → Fin f → RootRing f (r + a),
      restPrimeModel f r a c Q s e₁ p - restPrimeModel f r a c Q s e₂ p =
        Real.log p * (2 * ((p : ℝ) ^ m)⁻¹ *
          ((restTerm f (r + a) Q m τ (smallPowerSum f r a c (m - 1) τ') : ℚ) : ℝ)) := by
    intro Q
    have hin : ∀ σ : Fin f, ∀ k ∈ Icc 2 (r + a),
        (∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * k))⁻¹ *
            ((e₁ p (n + 1) σ k * restTerm f (r + a) Q k σ
              (smallPowerSum f r a c (k - 1) (s p (n + 1) σ)) : ℚ) : ℝ)) -
          ∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * k))⁻¹ *
            ((e₂ p (n + 1) σ k * restTerm f (r + a) Q k σ
              (smallPowerSum f r a c (k - 1) (s p (n + 1) σ)) : ℚ) : ℝ) =
        if σ = τ ∧ k = m then 2 * ((p : ℝ) ^ m)⁻¹ *
          ((restTerm f (r + a) Q m τ (smallPowerSum f r a c (m - 1) τ') : ℚ) : ℝ) else 0 := by
      intro σ k hk
      have hk1 : 1 ≤ k := by have := (Finset.mem_Icc.1 hk).1; omega
      have hs' : ∀ n : ℕ, s p (n + 1) σ = τ' := fun _ => rfl
      simp only [hs']
      have hs1 := summable_signed p hp2 k hk1
        (restTerm f (r + a) Q k σ (smallPowerSum f r a c (k - 1) τ'))
        (fun n => e₁ p (n + 1) σ k) (fun n => he₁ p (n + 1) σ k)
      have hs2 := summable_signed p hp2 k hk1
        (restTerm f (r + a) Q k σ (smallPowerSum f r a c (k - 1) τ'))
        (fun n => e₂ p (n + 1) σ k) (fun n => he₂ p (n + 1) σ k)
      rw [← hs1.tsum_sub hs2]
      have h0 : ∀ n : ℕ, n ≠ 0 →
          ((p : ℝ) ^ ((n + 1) * k))⁻¹ * ((e₁ p (n + 1) σ k *
            restTerm f (r + a) Q k σ (smallPowerSum f r a c (k - 1) τ') : ℚ) : ℝ) -
          ((p : ℝ) ^ ((n + 1) * k))⁻¹ * ((e₂ p (n + 1) σ k *
            restTerm f (r + a) Q k σ (smallPowerSum f r a c (k - 1) τ') : ℚ) : ℝ) = 0 := by
        intro n hn
        have hn1 : n + 1 ≠ 1 := by omega
        simp only [e₁, e₂, hn1, false_and, if_false, sub_self]
      rw [tsum_eq_single 0 h0]
      by_cases hστ : σ = τ ∧ k = m
      · obtain ⟨rfl, rfl⟩ := hστ
        simp only [e₁, e₂, zero_add, and_self, if_true, zero_add, one_mul]
        push_cast
        ring
      · have hne : ¬ (0 + 1 = 1 ∧ σ = τ ∧ k = m) := fun h => hστ h.2
        rw [if_neg hστ]
        simp only [e₁, e₂, if_neg hne]
        push_cast
        ring
    rw [restPrimeModel, restPrimeModel, ← mul_sub, ← sum_sub_distrib]
    congr 1
    have hσ : ∀ σ ∈ (univ : Finset (Fin f)), (∑ k ∈ Icc 2 (r + a), ∑' n : ℕ,
        ((p : ℝ) ^ ((n + 1) * k))⁻¹ * ((e₁ p (n + 1) σ k * restTerm f (r + a) Q k σ
          (smallPowerSum f r a c (k - 1) (s p (n + 1) σ)) : ℚ) : ℝ)) -
        ∑ k ∈ Icc 2 (r + a), ∑' n : ℕ,
        ((p : ℝ) ^ ((n + 1) * k))⁻¹ * ((e₂ p (n + 1) σ k * restTerm f (r + a) Q k σ
          (smallPowerSum f r a c (k - 1) (s p (n + 1) σ)) : ℚ) : ℝ) =
        ∑ k ∈ Icc 2 (r + a), if σ = τ ∧ k = m then 2 * ((p : ℝ) ^ m)⁻¹ *
          ((restTerm f (r + a) Q m τ (smallPowerSum f r a c (m - 1) τ') : ℚ) : ℝ) else 0 :=
      fun σ _ => by rw [← sum_sub_distrib]; exact sum_congr rfl (hin σ)
    rw [sum_congr rfl hσ]
    simp only [ite_and]
    rw [Fintype.sum_eq_single τ (fun σ hσ => by simp [hσ])]
    simp only [if_true]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_Icc.2 ⟨hm2, hmN⟩)]

  have hlin : ∀ t : ℚ, restTerm f (r + a) (Qt t) m τ (smallPowerSum f r a c (m - 1) τ') =
      restTerm f (r + a) Q₀ m τ (smallPowerSum f r a c (m - 1) τ') +
        t * restTerm f (r + a) S m τ (smallPowerSum f r a c (m - 1) τ') := by
    intro t
    simp only [restTerm, hQt]
    rw [mul_add, mul_smul_comm, flagIntegral_add_smul]
    ring

  set R₀ : ℝ := ((restTerm f (r + a) Q₀ m τ (smallPowerSum f r a c (m - 1) τ') : ℚ) : ℝ)
  set K : ℝ := Real.log p * (2 * ((p : ℝ) ^ m)⁻¹)
  have hK : 0 < K := by
    have : 0 < Real.log p := Real.log_pos (by exact_mod_cast (by omega : 1 < p))
    positivity
  have hslope : restTerm f (r + a) S m τ (smallPowerSum f r a c (m - 1) τ') = 0 := by
    by_contra hne
    set RS := restTerm f (r + a) S m τ (smallPowerSum f r a c (m - 1) τ')
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * Bnd / K + |R₀|)
    set t : ℚ := n / RS
    have h1 := hbd t e₁ he₁
    have h2 := hbd t e₂ he₂
    have hd := hdiff (Qt t)
    rw [hlin] at hd
    have htRS : t * RS = n := by simp only [t]; field_simp
    have hval : (((restTerm f (r + a) Q₀ m τ (smallPowerSum f r a c (m - 1) τ') +
        t * RS : ℚ)) : ℝ) = R₀ + n := by
      rw [htRS]; push_cast; rfl
    rw [hval] at hd
    have habs : |K * (R₀ + n)| ≤ 2 * Bnd := by
      rw [show K * (R₀ + n) = Real.log p * (2 * ((p : ℝ) ^ m)⁻¹ * (R₀ + n)) by ring, ← hd]
      calc _ ≤ |restPrimeModel f r a c (Qt t) s e₁ p| + |restPrimeModel f r a c (Qt t) s e₂ p| :=
            abs_sub _ _
        _ ≤ 2 * Bnd := by linarith
    rw [abs_mul, abs_of_pos hK] at habs
    have hR : (n : ℝ) - |R₀| ≤ |R₀ + n| := by
      have := abs_sub_abs_le_abs_sub (n : ℝ) (-R₀)
      rw [abs_neg, sub_neg_eq_add, add_comm] at this
      have hn0 : |(n : ℝ)| = n := abs_of_nonneg (by positivity)
      linarith
    have : 2 * Bnd / K < n - |R₀| := by linarith
    have h3 : 2 * Bnd < K * (n - |R₀|) := by
      rw [div_lt_iff₀ hK] at this; linarith
    nlinarith
  simp only [restTerm] at hslope
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  exact (mul_eq_zero.1 hslope).resolve_left hm0
end GroundTheory.Heights₂.Heights.RestTerms.RestBoundEq

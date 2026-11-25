-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_exists_forms_mem_of_not_le_relevant_cc722a823041
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:10:15.209126+00:00
-- url     : https://prove2.me/submissions/6b8fb3d0-68f4-49f0-838d-e991c3163fa2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PColonMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSectionNef
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_weight_blockWeight_3721b3973afe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_GradedFinite_proof_4a0254b94345
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ColonMultiHomog_proof_89514dc80a8c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MinimalPrimeMultiHomog_proof_00f169244e2b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SupSpanMultiHomog_proof_861d53cbe2c3


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open MvPolynomial NumbersDVR
noncomputable section
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type} [Field F]
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {J : Ideal (MRing ι F)} (hJ : IsMultiHomogIdeal J)
    (hrel : ∀ W : Ideal (MRing ι F), W.IsPrime → IsMultiHomogIdeal W → IsRelevant W → ¬ J ≤ W) :
    ∃ n : ℕ, ∀ m : K → ℕ, (∀ k, n * Fintype.card (ι k) < m k) →
      ∀ x : MRing ι F, IsMultiHomog x m → x ∈ J := by
  classical

  let e : (∀ k, ι k) → (Σ k, ι k) →₀ ℕ := fun σ =>
    Finsupp.equivFunOnFinite.symm (fun v => if v.2 = σ v.1 then 1 else 0)
  have he : ∀ σ v, e σ v = if v.2 = σ v.1 then 1 else 0 := fun σ v => rfl
  have hrad : ∀ σ : (∀ k, ι k), (monomial (e σ) (1 : F)) ∈ J.radical := by
    intro σ
    rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
    intro W hW
    have hWp : Ideal.IsPrime W := hW.1.1
    have hWh : IsMultiHomogIdeal W := MinimalPrimeMultiHomog.proof F K ι J W hJ hW
    obtain ⟨k, hk⟩ : ∃ k, ∀ i : ι k, (X ⟨k, i⟩ : MRing ι F) ∈ W := by
      by_contra h
      push Not at h
      exact hrel W hWp hWh h hW.1.2
    refine Ideal.mem_of_dvd _ ?_ (hk (σ k))
    rw [← pow_one (X _), X_pow_eq_monomial, monomial_dvd_monomial]
    refine ⟨Or.inr ?_, one_dvd _⟩
    rw [Finsupp.single_le_iff, he]
    simp
  have hrad' : ∀ σ : (∀ k, ι k), ∃ n : ℕ, (monomial (e σ) (1 : F)) ^ n ∈ J := fun σ => hrad σ
  choose N hN using hrad'
  refine ⟨Finset.univ.sup N, fun m hm x hx => ?_⟩
  rw [x.as_sum]
  refine Ideal.sum_mem _ fun d hd => ?_
  have hw := hx (mem_support_iff.mp hd)
  rw [Bridge.weight_blockWeight] at hw
  have hσ : ∀ k, ∃ i : ι k, Finset.univ.sup N ≤ d ⟨k, i⟩ := by
    intro k
    by_contra h
    push Not at h
    have h1 : ∑ i, d ⟨k, i⟩ ≤ ∑ _i : ι k, Finset.univ.sup N :=
      Finset.sum_le_sum fun i _ => (h i).le
    have h2 := congrFun hw k
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h1 h2
    have h3 := hm k
    rw [h2] at h1
    rw [mul_comm] at h3
    omega
  choose σ hσ using hσ
  have hmem : monomial (e σ) (1 : F) ^ Finset.univ.sup N ∈ J :=
    Ideal.pow_mem_of_pow_mem _ (hN σ) (Finset.le_sup (Finset.mem_univ σ))
  refine Ideal.mem_of_dvd _ ?_ hmem
  rw [monomial_pow, one_pow, monomial_dvd_monomial]
  refine ⟨Or.inr ?_, one_dvd _⟩
  intro v
  rw [Finsupp.smul_apply, he, smul_eq_mul]
  split_ifs with hv
  · obtain ⟨k, i⟩ := v
    simp only at hv
    subst hv
    simpa using hσ k
  · simp
end GroundTheory.Heights₂.Heights.Model

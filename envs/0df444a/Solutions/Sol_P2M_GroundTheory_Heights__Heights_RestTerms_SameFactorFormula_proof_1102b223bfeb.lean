-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SameFactorFormula_proof_1102b223bfeb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:02:37.322922+00:00
-- url     : https://prove2.me/submissions/ff4e3edc-e3b7-4b2d-91b1-903ee087090d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorFormula
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_smallPowerSum_508d420278d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockCoeff_rect_eq_7d9159b82c6d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_kappa_ne_zero_7c13c70c2d7e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_fibreDegree_eq_7b64163691ae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_smallPowerSum_mul_restPolynomial_d2f1e6c17816
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_sum_erase_const_5c346ca9300d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_dividedDifference_eq_of_hasDD_5f38fe8d41e9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_gmf_13295714a17c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_schur_1cba2d0c1248
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_mstar_mem_91aff65fe145
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_restrict_gmfOut_7b9edc99d122
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_toN_blockOut_b92d4fa800aa


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open Top MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SameFactorFormula
theorem _root_.solution (hA : LemmaA.Statement) (hB : LemmaB.Statement)
    (hF : FrobeniusCharacterFormula.Statement) (hCI : CharacterAtIdentity.Statement)
    (hV : VandermondeOfHomogeneous.Statement) (hRP : RectangleTablePos.Statement) :
    SameFactorFormula.Statement := by
  intro f r a c hf hr ha
  obtain ⟨κ, hκpm, hκ⟩ := hasDD_schur hB r a c
  obtain ⟨c0, hc0, hInt, hMain⟩ := hA f (r + a)
  have hκ0 := kappa_ne_zero hκpm
  have hra : r * a ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hfR : (numStandardTable (rectangle r a) : ℚ) ≠ 0 := by exact_mod_cast (hRP r a).ne'
  refine ⟨c0 * κ ^ f, mul_ne_zero hc0 (pow_ne_zero _ hκ0),
    fibreDegree_eq hF hCI hV f r a c hr ha κ hκ c0 hInt, ?_⟩
  intro Q hQ k hk2 hkN τ
  set q : Fin f → ℕ := fun σ => if σ = τ then k - 1 else 0 with hqdef
  have hGF := smallPowerSum_mul_restPolynomial f r a c k hk2 τ
  obtain ⟨P, hP, -, S', hS', hI⟩ := hMain _ Q hQ k (by omega) hkN τ _
    (by simpa using isHomogeneous_smallPowerSum f r a c (k - 1) τ)
  have hPeq : P = gmfOut f r a c κ q (f * (r * a) + 1) := by
    apply IsFractionRing.injective (RootRing f (r + a)) (FractionRing (RootRing f (r + a)))
    rw [hP, hGF, dividedDifference_eq_of_hasDD (hasDD_gmf hF f r a c κ hκ q _)]
  have hsum : ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') = (f - 1) * (r * a) := by
    rw [← sum_erase_const f τ (r * a)]
    exact Finset.sum_congr rfl fun σ hσ => by simp [hqdef, Finset.ne_of_mem_erase hσ]
  have hle : (f - 1) * (r * a) ≤ f * (r * a) + 1 :=
    (Nat.mul_le_mul_right _ (Nat.sub_le f 1)).trans (Nat.le_succ _)
  have hres := restrict_gmfOut f r a c κ q (f * (r * a) + 1) τ
    (fun σ hσ => by simp [hqdef, hσ]) (by rw [hsum]; exact hle)
  have hmτ : mstar f r a q (f * (r * a) + 1) τ τ = r * a + 1 := by
    simp only [mstar, if_true, hsum]
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rw [Nat.add_sub_cancel, add_mul, one_mul]
    omega
  have hms : mstar f r a q (f * (r * a) + 1) τ = fun σ => if σ = τ then r * a + 1 else r * a := by
    funext σ
    by_cases hσ : σ = τ
    · subst hσ; rw [hmτ, if_pos rfl]
    · simp [mstar, hσ, hqdef]
  have hqτ : q τ = k - 1 := by simp [hqdef]
  rw [hmτ, hqτ, toN_blockOut r a c κ (k - 1) (r * a + 1) k (by omega)] at hres
  have hprod : ∏ σ ∈ Finset.univ.erase τ,
      (blockCoeff (q σ) (r * a - q σ) (rectangle r a) * κ) =
      ((numStandardTable (rectangle r a) : ℚ) * κ) ^ (f - 1) := by
    rw [Finset.prod_congr rfl fun σ hσ => by
      rw [show q σ = 0 by simp [hqdef, Finset.ne_of_mem_erase hσ], Nat.sub_zero,
        blockCoeff_rect_eq hCI r a hra]]
    rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ τ), Finset.card_univ,
      Fintype.card_fin]
  have hmult : (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) =
      ((f * (r * a) + 1).factorial : ℚ) /
        (((r * a + 1).factorial : ℚ) * ((r * a).factorial : ℚ) ^ (f - 1)) := by
    have hp : ∏ σ, (mstar f r a q (f * (r * a) + 1) τ σ).factorial =
        (r * a + 1).factorial * (r * a).factorial ^ (f - 1) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), hmτ]
      congr 1
      rw [Finset.prod_congr rfl (fun σ hσ =>
        show (mstar f r a q (f * (r * a) + 1) τ σ).factorial = (r * a).factorial by
          simp only [hms, if_neg (Finset.ne_of_mem_erase hσ)]), Finset.prod_const,
        Finset.card_erase_of_mem (Finset.mem_univ τ), Finset.card_univ, Fintype.card_fin]
    have hs' := (Finset.mem_piAntidiag.mp
      (mstar_mem f r a q (f * (r * a) + 1) τ (by rw [hsum]; exact hle))).1
    have h := Nat.multinomial_spec (Finset.univ : Finset (Fin f))
      (mstar f r a q (f * (r * a) + 1) τ)
    rw [hp, hs'] at h
    have hden : ((r * a + 1).factorial : ℚ) * ((r * a).factorial : ℚ) ^ (f - 1) ≠ 0 := by positivity
    rw [eq_div_iff hden, ← h]
    push_cast
    ring
  set K : ℚ := (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) *
    ((numStandardTable (rectangle r a) : ℚ) * κ) ^ (f - 1) * κ with hK
  have hmultpos : (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.multinomial_pos _ _).ne'
  have hK0 : K ≠ 0 := by
    rw [hK]; exact mul_ne_zero (mul_ne_zero hmultpos (pow_ne_zero _ (mul_ne_zero hfR hκ0))) hκ0
  set T := ∑ nu ∈ partitionsOf r k,
      C (symmetricGroupCharacter (fun i => a + nu i) ((k - 1) :: List.replicate (r * a + 1) 1)) *
        aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) with hT
  have hTeq : ∑ nu ∈ partitionsOf r k, C (blockCoeff (k - 1) (r * a + 1) (fun i => a + nu i)) *
        aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) = T := by
    rw [hT]
    refine Finset.sum_congr rfl fun nu _ => ?_
    rw [blockCoeff, if_neg (by omega)]
  rw [hTeq, hprod] at hres
  have hPS : powerSumHom (r + a) S' = K • T := by
    rw [hS', hPeq, hres, hK, smul_eq_C_mul, smul_eq_C_mul]
    simp only [map_mul, map_pow]
    ring
  refine ⟨K⁻¹ • S', ?_, ?_⟩
  · rw [map_smul, hPS, smul_smul, inv_mul_cancel₀ hK0, one_smul]
  · rw [restTerm, hI, coeff_smul, smul_eq_mul]
    rw [hK, hmult]
    have hden : ((r * a + 1).factorial : ℚ) * ((r * a).factorial : ℚ) ^ (f - 1) ≠ 0 := by positivity
    have hnum : ((f * (r * a) + 1).factorial : ℚ) ≠ 0 := by positivity
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hden ⊢
    field_simp
    ring
end SameFactorFormula
end GroundTheory.Heights₂.Heights.RestTerms

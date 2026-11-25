-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_LinearTermValue_proof_f8c29a53c81a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:34:11.928873+00:00
-- url     : https://prove2.me/submissions/1ff53f9a-f526-45a7-8755-9ec49e7cee51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PLinearTermValue
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_partitionsOf_one_9cea0c74fd23
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_schur_rowOne_94c2ce3effa1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_powerSumHom_injective_b1bcc0d5fe5b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_dividedDifference_eq_of_hasDD_5f38fe8d41e9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_fibreDegree_eq_7b64163691ae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_gmf_13295714a17c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_schur_1cba2d0c1248
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_multinomial_const_2190c1ab2280
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
namespace LinearTermValue
theorem _root_.solution (hA : LemmaA.Statement) (hB : LemmaB.Statement)
    (hF : FrobeniusCharacterFormula.Statement) (hCI : CharacterAtIdentity.Statement)
    (hV : VandermondeOfHomogeneous.Statement) :
    LinearTermValue.Statement := by
  intro r a hr ha Q hQ
  obtain ⟨κ, hκpm, hκ⟩ := hasDD_schur hB r a .last
  obtain ⟨c0, hc0, hInt, hMain⟩ := hA 1 (r + a)
  have hra : r * a ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hJ := fibreDegree_eq hF hCI hV 1 r a .last hr ha κ hκ c0 hInt
  have hGF : (1 : RootRing 1 (r + a)) * restPolynomial 1 r a .last =
      gmf 1 r a .last 0 (1 * (r * a) + 1) := by
    simp [gmf, extraFactor, restPolynomial]
  obtain ⟨P, hP, -, S', hS', hI⟩ := hMain _ Q hQ 1 le_rfl (by omega) 0 1 (isHomogeneous_one _ _)
  have hPeq : P = gmfOut 1 r a .last κ 0 (1 * (r * a) + 1) := by
    apply IsFractionRing.injective (RootRing 1 (r + a)) (FractionRing (RootRing 1 (r + a)))
    rw [hP, hGF, dividedDifference_eq_of_hasDD (hasDD_gmf hF 1 r a .last κ hκ 0 _)]
  have herase : (Finset.univ : Finset (Fin 1)).erase 0 = ∅ := by decide
  have hres := restrict_gmfOut 1 r a .last κ 0 (1 * (r * a) + 1) 0
    (fun σ hσ => absurd (Subsingleton.elim σ 0) hσ) (by simp [herase])
  have hm : mstar 1 r a 0 (1 * (r * a) + 1) 0 = fun _ => r * a + 1 := by
    funext σ
    rw [Subsingleton.elim σ 0]
    simp [mstar, herase]
  rw [hm, herase, Finset.prod_empty, Pi.zero_apply,
    toN_blockOut r a .last κ 0 (r * a + 1) 1 (by omega), partitionsOf_one r hr,
    Finset.sum_singleton, schur_rowOne _ r hr] at hres
  have hmult : (Nat.multinomial Finset.univ (fun _ : Fin 1 => r * a + 1) : ℚ) = 1 := by
    rw [multinomial_const]
    have : ((r * a + 1).factorial : ℚ) ≠ 0 := by positivity
    simp [this]
  rw [hmult] at hres
  set b := blockCoeff 0 (r * a + 1) (fun i => a + rowOne r i) with hb
  have hb' : b = numStandardTable (fun i : Fin r => a + if (i : ℕ) = 0 then 1 else 0) := by
    rw [hb, blockCoeff, if_pos rfl, if_neg (by omega)]
    have h := hCI r (fun i => a + rowOne r i) (fun i j hij => by
      simp only [rowOne]
      split_ifs with h1 h2 <;> first | omega | (exfalso; have : (i : ℕ) ≤ j := hij; omega))
    have hs : ∑ i, (a + rowOne r i) = r * a + 1 := by
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      rw [Finset.sum_add_distrib, Fin.sum_univ_succ]
      simp [rowOne, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring
    rw [hs] at h
    exact h
  have hS'eq : S' = C (κ * b) * X (⟨0, by omega⟩ : Fin (r + a)) := by
    apply Flag.powerSumHom_injective
    rw [hS', hPeq, hres]
    simp only [powerSumHom, map_mul, aeval_C, aeval_X, algebraMap_eq, psum, map_sum,
      SmallBlock.sign, map_one, one_mul, one_smul, zero_add, pow_one]
    first | done | ring
  rw [hS'eq, one_mul] at hI
  rw [hI, hJ]
  simp only [coeff_C_mul, coeff_X, mul_one]
  rw [← hb']
  have h01 : (⟨1 - 1, by omega⟩ : Fin (r + a)) = ⟨0, by omega⟩ := rfl
  have hfac : ((r * a).factorial : ℚ) ≠ 0 := by positivity
  field_simp
  simp only [if_true, mul_one, one_mul]
end LinearTermValue
end GroundTheory.Heights₂.Heights.RestTerms

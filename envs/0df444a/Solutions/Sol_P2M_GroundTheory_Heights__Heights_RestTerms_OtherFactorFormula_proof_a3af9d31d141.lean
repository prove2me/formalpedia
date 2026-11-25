-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_OtherFactorFormula_proof_a3af9d31d141
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:34:07.745454+00:00
-- url     : https://prove2.me/submissions/e9c641c8-33e1-41ba-8fe8-5df0cec44cbf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_POtherFactorFormula
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_isSymmetric_aeval_smul_X_3d12ee5aa775
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_k_sub_one_le_0ea464919331
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_exists_powerSumHom_eq_7cf93073418c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_powerSumHom_injective_b1bcc0d5fe5b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_schur_isSymmetric_e777444d0d85
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_antitone_of_mem_partitionsOf_9fba049ce9d8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockCoeff_rect_eq_7d9159b82c6d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_dividedDifference_eq_of_hasDD_5f38fe8d41e9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_fibreDegree_eq_7b64163691ae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_gmf_13295714a17c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_schur_1cba2d0c1248
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_smallPowerSum_508d420278d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_kappa_ne_zero_7c13c70c2d7e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_mstar_mem_91aff65fe145
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_restrict_gmfOut_7b9edc99d122
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_smallPowerSum_mul_restPolynomial_d2f1e6c17816
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_sum_of_mem_partitionsOf_e2ce5534b3c3
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
namespace OtherFactorFormula
theorem _root_.solution (hA : LemmaA.Statement) (hB : LemmaB.Statement)
    (hF : FrobeniusCharacterFormula.Statement) (hCI : CharacterAtIdentity.Statement)
    (hV : VandermondeOfHomogeneous.Statement) (hRP : RectangleTablePos.Statement) :
    OtherFactorFormula.Statement := by
  intro f r a c hf hr ha
  obtain ⟨κ, hκpm, hκ⟩ := hasDD_schur hB r a c
  obtain ⟨c0, hc0, hInt, hMain⟩ := hA f (r + a)
  have hκ0 := kappa_ne_zero hκpm
  have hra : r * a ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hfR : (numStandardTable (rectangle r a) : ℚ) ≠ 0 := by exact_mod_cast (hRP r a).ne'
  refine ⟨c0 * κ ^ f, mul_ne_zero hc0 (pow_ne_zero _ hκ0),
    fibreDegree_eq hF hCI hV f r a c hr ha κ hκ c0 hInt, ?_⟩
  intro Q hQ k hk2 hkN τ τ' hττ'
  have hk1 := k_sub_one_le r a k hr ha hkN
  set q : Fin f → ℕ := fun σ => if σ = τ' then k - 1 else 0 with hqdef
  have hGF := smallPowerSum_mul_restPolynomial f r a c k hk2 τ'
  obtain ⟨P, hP, -, S', hS', hI⟩ := hMain _ Q hQ k (by omega) hkN τ _
    (by simpa using isHomogeneous_smallPowerSum f r a c (k - 1) τ')
  have hPeq : P = gmfOut f r a c κ q (f * (r * a) + 1) := by
    apply IsFractionRing.injective (RootRing f (r + a)) (FractionRing (RootRing f (r + a)))
    rw [hP, hGF, dividedDifference_eq_of_hasDD (hasDD_gmf hF f r a c κ hκ q _)]
  have hτ'mem : τ' ∈ Finset.univ.erase τ := Finset.mem_erase.mpr ⟨hττ', Finset.mem_univ τ'⟩
  have hsum : ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') = (f - 1) * (r * a) - (k - 1) := by
    rw [← Finset.add_sum_erase _ _ hτ'mem]
    have h2 : ∑ σ' ∈ (Finset.univ.erase τ).erase τ', (r * a - q σ') = (f - 2) * (r * a) := by
      rw [Finset.sum_congr rfl (fun σ hσ => show r * a - q σ = r * a by
        simp [hqdef, Finset.ne_of_mem_erase hσ]), Finset.sum_const,
        Finset.card_erase_of_mem hτ'mem, Finset.card_erase_of_mem (Finset.mem_univ τ),
        Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      congr 1
    rw [h2]
    simp only [hqdef, if_true]
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by omega⟩
    simp only [Nat.add_sub_cancel, show f' + 2 - 1 = f' + 1 by omega]
    rw [add_mul, one_mul]
    omega
  have hle : (f - 1) * (r * a) - (k - 1) ≤ f * (r * a) + 1 :=
    (Nat.sub_le _ _).trans ((Nat.mul_le_mul_right _ (Nat.sub_le f 1)).trans (Nat.le_succ _))
  have hres := restrict_gmfOut f r a c κ q (f * (r * a) + 1) τ
    (fun σ hσ => by simp only [hqdef]; split_ifs <;> omega) (by rw [hsum]; exact hle)
  have hmτ : mstar f r a q (f * (r * a) + 1) τ τ = r * a + k := by
    simp only [mstar, if_true, hsum]
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by omega⟩
    simp only [show f' + 2 - 1 = f' + 1 by omega]
    have h3 : r * a ≤ (f' + 1) * (r * a) := Nat.le_mul_of_pos_left _ (by omega)
    rw [show (f' + 2) * (r * a) = (f' + 1) * (r * a) + r * a by ring]
    omega
  have hms : mstar f r a q (f * (r * a) + 1) τ = fun σ =>
      if σ = τ then r * a + k else if σ = τ' then r * a - (k - 1) else r * a := by
    funext σ
    by_cases hσ : σ = τ
    · subst hσ; rw [hmτ, if_pos rfl]
    · by_cases hσ' : σ = τ'
      · subst hσ'; simp [mstar, hσ, hqdef]
      · simp [mstar, hσ, hσ', hqdef]
  have hqτ : q τ = 0 := by simp [hqdef, Ne.symm hττ']
  rw [hmτ, hqτ, toN_blockOut r a c κ 0 (r * a + k) k (by omega)] at hres
  set χR := symmetricGroupCharacter (rectangle r a) ((k - 1) :: List.replicate (r * a - (k - 1)) 1)
    with hχR
  have hprod : ∏ σ ∈ Finset.univ.erase τ,
      (blockCoeff (q σ) (r * a - q σ) (rectangle r a) * κ) =
      (χR * κ) * ((numStandardTable (rectangle r a) : ℚ) * κ) ^ (f - 2) := by
    rw [← Finset.mul_prod_erase _ _ hτ'mem]
    congr 1
    · simp only [hqdef, if_true]
      rw [blockCoeff, if_neg (by omega)]
    · rw [Finset.prod_congr rfl fun σ hσ => by
        rw [show q σ = 0 by simp [hqdef, Finset.ne_of_mem_erase hσ], Nat.sub_zero,
          blockCoeff_rect_eq hCI r a hra]]
      rw [Finset.prod_const, Finset.card_erase_of_mem hτ'mem,
        Finset.card_erase_of_mem (Finset.mem_univ τ), Finset.card_univ, Fintype.card_fin]
      congr 1
  have hmult : (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) =
      ((f * (r * a) + 1).factorial : ℚ) /
        (((r * a + k).factorial : ℚ) * ((r * a - (k - 1)).factorial : ℚ) *
          ((r * a).factorial : ℚ) ^ (f - 2)) := by
    have hp : ∏ σ, (mstar f r a q (f * (r * a) + 1) τ σ).factorial =
        (r * a + k).factorial * ((r * a - (k - 1)).factorial * (r * a).factorial ^ (f - 2)) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), hmτ, ← Finset.mul_prod_erase _ _ hτ'mem]
      congr 2
      · simp only [hms, if_neg hττ', if_true]
      · rw [Finset.prod_congr rfl (fun σ hσ =>
          show (mstar f r a q (f * (r * a) + 1) τ σ).factorial = (r * a).factorial by
            simp only [hms, if_neg (Finset.ne_of_mem_erase hσ),
              if_neg (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hσ))]), Finset.prod_const,
          Finset.card_erase_of_mem hτ'mem, Finset.card_erase_of_mem (Finset.mem_univ τ),
          Finset.card_univ, Fintype.card_fin]
        congr 1
    have hs' := (Finset.mem_piAntidiag.mp
      (mstar_mem f r a q (f * (r * a) + 1) τ (by rw [hsum]; exact hle))).1
    have h := Nat.multinomial_spec (Finset.univ : Finset (Fin f))
      (mstar f r a q (f * (r * a) + 1) τ)
    rw [hp, hs'] at h
    have hden : ((r * a + k).factorial : ℚ) * ((r * a - (k - 1)).factorial : ℚ) *
        ((r * a).factorial : ℚ) ^ (f - 2) ≠ 0 := by positivity
    rw [eq_div_iff hden, ← h]
    push_cast
    ring
  set T := ∑ nu ∈ partitionsOf r k,
      C ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) *
        aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) with hT
  have hTeq : ∑ nu ∈ partitionsOf r k, C (blockCoeff 0 (r * a + k) (fun i => a + nu i)) *
        aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) = T := by
    rw [hT]
    refine Finset.sum_congr rfl fun nu hnu => ?_
    rw [blockCoeff, if_pos rfl, if_neg (by omega)]
    have hs := sum_of_mem_partitionsOf hnu
    have hanti := antitone_of_mem_partitionsOf hnu
    have h := hCI r (fun i => a + nu i) (fun i j hij => Nat.add_le_add_left (hanti hij) a)
    have hs2 : ∑ i, (a + nu i) = r * a + k := by
      rw [Finset.sum_add_distrib, hs]
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_comm]
    rw [hs2] at h
    rw [h]
  rw [hTeq, hprod] at hres
  have hTsym : T.IsSymmetric := by
    intro e
    rw [hT, map_sum]
    refine Finset.sum_congr rfl fun nu _ => ?_
    rw [map_mul, rename_C, isSymmetric_aeval_smul_X _ (Schur.schur_isSymmetric _) e]
  set K : ℚ := (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) *
    ((χR * κ) * ((numStandardTable (rectangle r a) : ℚ) * κ) ^ (f - 2)) * κ with hK
  have hPS : powerSumHom (r + a) S' = K • T := by
    rw [hS', hPeq, hres, hK, smul_eq_C_mul, smul_eq_C_mul]
    simp only [map_mul, map_pow]
    ring
  have hmultpos : (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.multinomial_pos _ _).ne'
  by_cases hχ : χR = 0
  · obtain ⟨S, hS⟩ := Flag.exists_powerSumHom_eq hTsym
    have hS'0 : S' = 0 := by
      apply Flag.powerSumHom_injective
      rw [hPS, hK, hχ, map_zero]
      simp
    refine ⟨S, hS, ?_⟩
    rw [restTerm, hI, hS'0, coeff_zero, hχ]
    ring
  · have hK0 : K ≠ 0 := by
      rw [hK]
      exact mul_ne_zero (mul_ne_zero hmultpos (mul_ne_zero (mul_ne_zero hχ hκ0)
        (pow_ne_zero _ (mul_ne_zero hfR hκ0)))) hκ0
    refine ⟨K⁻¹ • S', ?_, ?_⟩
    · rw [map_smul, hPS, smul_smul, inv_mul_cancel₀ hK0, one_smul]
    · rw [restTerm, hI, coeff_smul, smul_eq_mul]
      rw [hK, hmult]
      have hden : ((r * a + k).factorial : ℚ) * ((r * a - (k - 1)).factorial : ℚ) *
          ((r * a).factorial : ℚ) ^ (f - 2) ≠ 0 := by positivity
      have hnum : ((f * (r * a) + 1).factorial : ℚ) ≠ 0 := by positivity
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by omega⟩
      simp only [Nat.add_sub_cancel] at hden ⊢
      field_simp
      ring
end OtherFactorFormula
end GroundTheory.Heights₂.Heights.RestTerms

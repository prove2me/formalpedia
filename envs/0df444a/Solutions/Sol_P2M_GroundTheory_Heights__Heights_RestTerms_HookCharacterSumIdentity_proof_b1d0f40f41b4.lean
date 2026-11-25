-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_HookCharacterSumIdentity_proof_b1d0f40f41b4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:39:08.381212+00:00
-- url     : https://prove2.me/submissions/a346a589-6678-4188-a113-610949321c92

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHookCharacterSumIdentity
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_sum_hooks_238955aa420b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_powerSumHom_injective_b1bcc0d5fe5b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_antitone_of_mem_partitionsOf_9fba049ce9d8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_sum_of_mem_partitionsOf_e2ce5534b3c3


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
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace HookCharacterSumIdentity
theorem _root_.solution (hSh : ShiftSumRule.Statement)
    (hL : LinearTermValue.Statement) (hF : SameFactorFormula.Statement)
    (hS : SchurSignCoefficient.Statement) (hR : RectangleTablePos.Statement)
    (hD : RestPolynomialDecomposes.Statement) : HookCharacterSumIdentity.Statement := by
  intro r a hr ha
  obtain ⟨Q, hQ⟩ := hD 1 r a .last
  obtain ⟨C₀, hC₀, hJ, hT⟩ := hF 1 r a .last le_rfl hr ha
  have hfR : (numStandardTable (rectangle r a) : ℚ) ≠ 0 := by exact_mod_cast (hR r a).ne'
  have hJ' : fibreDegree 1 r a .last = C₀ * numStandardTable (rectangle r a) := by
    rw [hJ]
    have : ((r * a).factorial : ℚ) ≠ 0 := by positivity
    rw [one_mul, pow_one, pow_one]
    field_simp
  have hterm : ∀ k ∈ Finset.Icc 2 (r + a),
      restTerm 1 (r + a) Q k 0 (smallPowerSum 1 r a .last (k - 1) 0) =
        C₀ * ∑ l ∈ Finset.range (min r k), (-1 : ℚ) ^ l *
          symmetricGroupCharacter (fun i => a + hookShape r k l i)
            ((k - 1) :: List.replicate (r * a + 1) 1) := by
    intro k hk
    obtain ⟨hk2, hkN⟩ := Finset.mem_Icc.mp hk
    obtain ⟨S, hS1, hS2⟩ := hT Q hQ k hk2 hkN 0
    have hex := fun nu (hnu : nu ∈ partitionsOf r k) =>
      hS (r + a) r k (by omega) hkN nu 1 (Or.inl rfl) (Top.antitone_of_mem_partitionsOf hnu)
        (Top.sum_of_mem_partitionsOf hnu)
    choose! Sν hSν1 hSν2 using hex
    have hSeq : S = ∑ nu ∈ partitionsOf r k,
        C (symmetricGroupCharacter (fun i => a + nu i) ((k - 1) :: List.replicate (r * a + 1) 1)) *
          Sν nu := by
      apply Flag.powerSumHom_injective
      rw [hS1, map_sum]
      refine Finset.sum_congr rfl fun nu hnu => ?_
      rw [map_mul, hSν1 nu hnu]
      simp [powerSumHom, SmallBlock.sign]
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have hcoeff : (k : ℚ) * coeff (Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1) S =
        ∑ nu ∈ partitionsOf r k,
          symmetricGroupCharacter (fun i => a + nu i) ((k - 1) :: List.replicate (r * a + 1) 1) *
            (if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then
              (-1 : ℚ) ^ ((Finset.univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card)
            else 0) := by
      rw [hSeq, coeff_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun nu hnu => ?_
      rw [coeff_C_mul, hSν2 nu hnu, one_pow, one_mul]
      split_ifs
      · field_simp
      · simp
    have hh := HookSum.sum_hooks r k (by omega)
      (fun nu => symmetricGroupCharacter (fun i => a + nu i) ((k - 1) :: List.replicate (r * a + 1) 1))
    beta_reduce at hh
    rw [hS2, ← hh, ← hcoeff]
    have : ((r * a + 1).factorial : ℚ) ≠ 0 := by positivity
    simp only [one_mul, Nat.sub_self, pow_zero, mul_one]
    field_simp
  have hsh := hSh r a hr ha Q hQ
  have hlin := hL r a hr ha Q hQ
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hsh
  rw [hJ'] at hlin
  apply mul_left_cancel₀ (mul_ne_zero hC₀ hfR)
  linear_combination (-(a : ℚ)) * hlin + (numStandardTable (rectangle r a) : ℚ) * hsh
end HookCharacterSumIdentity
end GroundTheory.Heights₂.Heights.RestTerms

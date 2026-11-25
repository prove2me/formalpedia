-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_OtherFactorBound_proof_d9ec121f6930
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:31:56.0328+00:00
-- url     : https://prove2.me/submissions/9224cd25-2b6a-4d51-adbb-d7551b63c277

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_POtherFactorBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_OtherFactorBound_add_le_mul_add_one_a38988a5c202
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_OtherFactorBound_coeff_bound_c07558531dc0

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
namespace OtherFactorBound
theorem _root_.solution (hO : OtherFactorFormula.Statement)
    (hF : SameFactorFormula.Statement) (hS : SchurSignCoefficient.Statement)
    (hB : CharacterBound.Statement) (hH : HookSumBound.Statement)
    (hR : RectangleTablePos.Statement) (hD : RestPolynomialDecomposes.Statement) :
    OtherFactorBound.Statement := by
  intro f r a c hf hr ha
  have hP : (0 : ℚ) < numStandardTable (rectangle r a) := by exact_mod_cast hR r a
  have hkey := OtherFactorBound.add_le_mul_add_one hr ha
  refine ⟨?_, hD f r a c, ?_⟩
  · obtain ⟨C₀, hC₀, hJ, -⟩ := hF f r a c hf hr ha
    rw [hJ]
    have h1 : ((f * (r * a)).factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((r * a).factorial : ℚ) ≠ 0 := by positivity
    have := hP.ne'
    simp_all
  intro Q hQ k hk2 hkN τ τ' hne
  have hk1 : k - 1 ≤ r * a := by omega
  refine ⟨fun h => absurd h (by omega), ?_⟩
  have hf2 : 2 ≤ f := by
    by_contra h
    have : f = 1 := by omega
    subst this
    exact hne (Subsingleton.elim _ _)
  obtain ⟨C₀, hC₀, hJ, hT⟩ := hO f r a c hf2 hr ha
  obtain ⟨S, hSeq, hTk⟩ := hT Q hQ k hk2 hkN τ τ' hne
  have hcoef := OtherFactorBound.coeff_bound hS hH r a k c (by omega) hkN S hSeq
  have hchi := hB r (rectangle r a) ((k - 1) :: List.replicate (r * a - (k - 1)) 1)
    (fun _ _ _ => le_rfl) (by
      intro q hq
      simp only [List.mem_cons, List.mem_replicate] at hq
      omega)
  rw [hTk, hJ]
  set y := coeff (Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1) S
  set z := symmetricGroupCharacter (rectangle r a) ((k - 1) :: List.replicate (r * a - (k - 1)) 1)
  set P : ℚ := (numStandardTable (rectangle r a) : ℚ) with hPdef
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
  have hg : g + 2 - 2 = g := by omega
  rw [hg]

  set n1 := r * a with hn1
  set n := (g + 2) * n1 with hn
  have hD1 : ((n1 + k).factorial : ℚ) =
      (Nat.choose (n1 + k) k : ℚ) * (k.factorial : ℚ) * (n1.factorial : ℚ) := by
    have := Nat.add_choose_mul_factorial_mul_factorial n1 k
    rw [← this]; push_cast; ring
  have hA : (n1.factorial : ℚ) =
      ((n1 - (k - 1)).factorial : ℚ) * (n1.descFactorial (k - 1) : ℚ) := by
    exact_mod_cast (Nat.factorial_mul_descFactorial hk1).symm
  have hM : ((n + 1).factorial : ℚ) = ((n + 1 : ℕ) : ℚ) * (n.factorial : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hdesc : (0 : ℚ) < n1.descFactorial (k - 1) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hk1
  have hchoose : (0 : ℚ) < Nat.choose (n1 + k) k := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hBpos : (0 : ℚ) < (n1 - (k - 1)).factorial := by positivity
  have hKpos : (0 : ℚ) < k.factorial := by positivity
  have hnpos : (0 : ℚ) < n.factorial := by positivity
  have hkpos : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)

  have hstep : |C₀ * k * ((n + 1).factorial : ℚ) /
        (((n1 + k).factorial : ℚ) * ((n1 - (k - 1)).factorial : ℚ) *
          ((n1).factorial : ℚ) ^ g) * P ^ g * z * y| ≤
      ((n + 1 : ℕ) : ℚ) * |C₀ * (n.factorial : ℚ) / ((n1).factorial : ℚ) ^ (g + 2) * P ^ (g + 2)| *
        ((n1.descFactorial (k - 1) : ℚ) * 2 ^ (k - 1)) / (k.factorial : ℚ) := by
    rw [hD1, hM]
    have hApos : (0 : ℚ) < n1.factorial := by positivity
    simp only [abs_mul, abs_div, abs_pow, Nat.abs_cast, abs_of_pos hP]
    have hX1 : 0 ≤ |C₀| * (k : ℚ) * (((n + 1 : ℕ) : ℚ) * (n.factorial : ℚ)) /
        ((Nat.choose (n1 + k) k : ℚ) * (k.factorial : ℚ) * (n1.factorial : ℚ) *
          ((n1 - (k - 1)).factorial : ℚ) * (n1.factorial : ℚ) ^ g) * P ^ g := by positivity
    refine (mul_le_mul (mul_le_mul_of_nonneg_left hchi hX1) hcoef (abs_nonneg _)
      (by positivity)).trans (le_of_eq ?_)
    field_simp
    rw [hA]
    ring
  refine hstep.trans ?_

  have hX : (n1.descFactorial (k - 1) : ℚ) * 2 ^ (k - 1) ≤ restX r a ^ (k - 1) := by
    have h1 : (n1.descFactorial (k - 1) : ℚ) ≤ (n1 : ℚ) ^ (k - 1) := by
      exact_mod_cast Nat.descFactorial_le_pow n1 (k - 1)
    have h2 : (2 * (n1 : ℚ)) ≤ restX r a := by
      simp only [restX, hn1]; push_cast; nlinarith [(Nat.cast_nonneg (r + a : ℕ) : (0 : ℚ) ≤ _)]
    calc (n1.descFactorial (k - 1) : ℚ) * 2 ^ (k - 1)
        ≤ (n1 : ℚ) ^ (k - 1) * 2 ^ (k - 1) := by gcongr
      _ = (2 * (n1 : ℚ)) ^ (k - 1) := by ring
      _ ≤ restX r a ^ (k - 1) := by gcongr
  have hpos1 : 0 ≤ ((n + 1 : ℕ) : ℚ) := by positivity
  gcongr
end OtherFactorBound
end GroundTheory.Heights₂.Heights.RestTerms

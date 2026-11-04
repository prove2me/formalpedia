-- Prove2me | solution 1 for ThreeSum.LightPrimePool.mem_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:06:31.82576+00:00
-- url     : https://prove2.me/submissions/4ac96cd6-bb25-42b3-86a5-af363755514c

import Definitions.Def_Submission_ThreeSum_LightPrimality
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_WeightedScore
import Mathlib.NumberTheory.Bertrand
import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_replicate_zero
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_WeightedScore_corrections_zero
import Theorems.Thm_ThreeSum_WeightedScore_remaining_zero
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.CyclicFold.asPolynomial_replicate_zero
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.minus_getD
attribute [local simp] ThreeSum.Karatsuba.plus_getD
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.WeightedScore.corrections_zero
attribute [local simp] ThreeSum.WeightedScore.remaining_zero



set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimePool
open Light
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.LightPrimePool
theorem _root_.solution {y i p : ℕ} :
    p ∈ scanned y i ↔ Nat.Prime p ∧ y < p ∧ p ≤ y+i := by
  induction i with
  | zero => simp only [scanned,List.not_mem_nil,false_iff]; omega
  | succ i ih =>
      by_cases hp : Nat.Prime (y+i+1)
      · simp only [scanned,if_pos hp,List.mem_append,List.mem_singleton,ih]
        constructor
        · rintro (⟨hpr,hlo,hhi⟩ | rfl)
          · exact ⟨hpr,hlo,by omega⟩
          · exact ⟨hp,by omega,by omega⟩
        · rintro ⟨hpr,hlo,hhi⟩
          by_cases heq : p = y+i+1
          · exact Or.inr heq
          · exact Or.inl ⟨hpr,hlo,by omega⟩
      · simp only [scanned,if_neg hp,ih]
        constructor
        · rintro ⟨hpr,hlo,hhi⟩
          exact ⟨hpr,hlo,by omega⟩
        · rintro ⟨hpr,hlo,hhi⟩
          have hne : p ≠ y+i+1 := fun heq => hp (heq ▸ hpr)
          exact ⟨hpr,hlo,by omega⟩
end ThreeSum.LightPrimePool

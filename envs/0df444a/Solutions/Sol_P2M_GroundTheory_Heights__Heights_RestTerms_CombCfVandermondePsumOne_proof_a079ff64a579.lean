-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CombCfVandermondePsumOne_proof_a079ff64a579
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:36:57.292504+00:00
-- url     : https://prove2.me/submissions/bd9c6839-11ea-40e2-b155-dbae28add58c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombCfVandermondePsumOne
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_alt_eq_sum_69324f4b2849
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_sum_377f06929651
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_zsmul_84a2d79b925d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_vandermondeOf_X_eq_alt_52fd29888339


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
open MvPolynomial Finset Equiv Comb
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace CombCfVandermondePsumOne
theorem _root_.solution (h1 : CombCfMonomialPsumOne.Statement)
    (h2 : CombDetDescFactorial.Statement) : CombCfVandermondePsumOne.Statement := by
  intro m n l hl
  have hA : alternantPsum m (List.replicate n 1) = alt (stair m) * psum (Fin m) ℚ 1 ^ n := by
    simp only [alternantPsum, List.map_replicate, List.prod_replicate, vandermondeOf_X_eq_alt]
  have hterm : ∀ σ : Perm (Fin m),
      cf l (monomial (ex (stair m ∘ σ.symm)) (1 : ℚ) * psum (Fin m) ℚ 1 ^ n) =
        ((n.factorial : ℚ) / ∏ i, ((l i).factorial : ℚ)) *
          ∏ i, ((l i).descFactorial (stair m (σ.symm i)) : ℚ) := by
    intro σ
    rw [h1]
    have hsum : ∑ i, l i = ∑ i, (stair m ∘ σ.symm) i + n := by
      rw [hl, Function.comp_def, Equiv.sum_comp σ.symm (stair m)]
    by_cases hle : ∀ i, (stair m ∘ σ.symm) i ≤ l i
    · rw [if_pos ⟨hle, hsum⟩]
      have hd : ∀ i, ((l i).descFactorial (stair m (σ.symm i)) : ℚ) =
          ((l i).factorial : ℚ) / ((l i - stair m (σ.symm i)).factorial : ℚ) := by
        intro i
        rw [eq_div_iff (by positivity), mul_comm]
        exact_mod_cast Nat.factorial_mul_descFactorial (hle i)
      simp only [hd, Finset.prod_div_distrib, Function.comp_apply]
      have hp : (∏ i, ((l i).factorial : ℚ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i _ => by positivity
      have hq : (∏ i, ((l i - stair m (σ.symm i)).factorial : ℚ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i _ => by positivity
      field_simp
    · rw [if_neg (fun h => hle h.1)]
      push Not at hle
      obtain ⟨i, hi⟩ := hle
      simp only [Function.comp_apply] at hi
      have h0 : ∏ j, ((l j).descFactorial (stair m (σ.symm j)) : ℚ) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Nat.descFactorial_eq_zero_iff_lt.mpr hi])
      rw [h0, mul_zero]
  have hdet : ∑ σ : Perm (Fin m), ((Perm.sign σ : ℤ) : ℚ) *
      ∏ i, ((l i).descFactorial (stair m (σ.symm i)) : ℚ) = vandermondeOf (fun i => (l i : ℚ)) := by
    rw [← h2 m l, Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul, ← Equiv.prod_comp σ]
    simp
  rw [hA, alt_eq_sum, Finset.sum_mul, cf_sum]
  simp_rw [smul_mul_assoc, cf_zsmul, hterm]
  calc _ = ((n.factorial : ℚ) / ∏ i, ((l i).factorial : ℚ)) * ∑ σ : Perm (Fin m),
        ((Perm.sign σ : ℤ) : ℚ) * ∏ i, ((l i).descFactorial (stair m (σ.symm i)) : ℚ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    _ = _ := by rw [hdet]; ring
end CombCfVandermondePsumOne
end GroundTheory.Heights₂.Heights.RestTerms

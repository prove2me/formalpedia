-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_LemmaB_proof_ccf90bd04f01
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:53:59.420943+00:00
-- url     : https://prove2.me/submissions/3f3cb459-0dc6-4eac-9652-81bdd8b12bc8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltPush
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PLemmaB
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_antisymmetrize_C_mul_9a5d169b441b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_blockVandermonde_ne_zero_90c17aff8bcb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_antisym_rename_mul_rename_356f52824e82


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
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace LemmaB
theorem _root_.solution (h1 : SchAevalSignedRename.Statement) (h2 : SchAntisymmetrizePlace.Statement)
    (h3 : SchSmallBlockProduct.Statement) (h4 : SchConcatAlternant.Statement)
    (h5 : SchConcatAlternantZero.Statement) (h6 : SchBlockVandermondeOne.Statement)
    (h7 : SchSchurHomogeneous.Statement) : LemmaB.Statement := by
  intro r a c
  obtain ⟨s, hs, hconc⟩ := h4 r a c
  have hsgn : ∀ n : ℕ, c.sign ^ n = 1 ∨ c.sign ^ n = -1 := by
    intro n
    cases c <;> simp [SmallBlock.sign, neg_one_pow_eq_or]
  refine ⟨s * ((r.factorial : ℚ) * a.factorial) * c.sign ^ (r * (r - 1) / 2 + r * a), ?_, ?_⟩
  · rcases hs with rfl | rfl <;> rcases hsgn (r * (r - 1) / 2 + r * a) with h | h <;>
      rw [h] <;> first | (left; ring1) | (right; ring1)
  intro lam hlam
  have hV : algebraMap (RootRing 1 (r + a)) (FractionRing (RootRing 1 (r + a)))
      (blockVandermonde 1 (r + a)) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (blockVandermonde_ne_zero 1 (r + a))
  unfold dividedDifference
  rw [h3, antisymmetrize_C_mul, h2, KAlt.antisym_rename_mul_rename, map_smul]
  split_ifs with hcont
  · rw [hconc lam hcont, div_eq_iff hV, ← map_mul]
    congr 1
    have hA := h1 (Fin (r + a)) (Fin 1 × Fin (r + a)) c.sign (fun i => ((0 : Fin 1), i))
      (∑ i, (lam i - a)) (schur (Fin (r + a)) (fun i : Fin r => lam i - a))
      (h7 (Fin (r + a)) r (fun i : Fin r => lam i - a))
    have hsum : ∑ i, lam i = ∑ i, (lam i - a) + r * a := by
      rw [show r * a = ∑ _i : Fin r, a by simp, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => (Nat.sub_add_cancel (hcont i)).symm
    rw [hA, h6, map_mul, hsum, smul_eq_C_mul]
    simp only [map_mul, map_pow, map_natCast]
    ring
  · rw [h5 r a lam hlam hcont, map_zero, smul_zero, mul_zero, map_zero, zero_div]
end LemmaB
end GroundTheory.Heights₂.Heights.RestTerms

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagVandermondeDvd_proof_50a8090ceaac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:53:39.78982+00:00
-- url     : https://prove2.me/submissions/9217f036-cf9e-4ca8-8e42-7743b1626f1c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagVandermondeDvd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagVandermondeDvd_blockVandermonde_eq_prod_643e36086d8c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagVandermondeDvd_rename_swap_eq_c2b89be0fe92
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagVandermondeDvd_blockSign_update_swap_540d64528759

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
open FlagVandermondeDvd
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FlagVandermondeDvd
theorem _root_.solution (h1 : FlagSwapDivisible.Statement) (h2 : FlagDiffPrime.Statement)
    (h3 : FlagDiffNotDvd.Statement) (h4 : FlagProdPrimesDvd.Statement) :
    FlagVandermondeDvd.Statement := by
  intro f N P hP
  rw [blockVandermonde_eq_prod]
  refine h4 (RootRing f N) (Fin f × Fin N × Fin N) _ _ P ?_ ?_ ?_
  · rintro ⟨τ, i, j⟩ ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    exact h2 _ _ _ (by simp [ht.ne])
  · rintro ⟨τ, i, j⟩ ht ⟨τ', i', j'⟩ ht' hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ht'
    refine h3 _ _ _ _ _ (by simp [ht.ne]) (by simp [ht'.ne]) ?_ ?_
    · rintro ⟨ha, hb⟩
      simp only [Prod.mk.injEq] at ha hb
      exact hne (by rw [ha.1, ha.2, hb.2])
    · rintro ⟨ha, hb⟩
      simp only [Prod.mk.injEq] at ha hb
      rw [ha.2, hb.2] at ht
      exact absurd (ht.trans ht') (lt_irrefl _)
  · rintro ⟨τ, i, j⟩ ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    refine h1 _ P _ _ (by simp [ht.ne]) ?_
    rw [rename_swap_eq, hP, blockSign_update_swap f N τ i j ht.ne, neg_one_smul]
end FlagVandermondeDvd
end GroundTheory.Heights₂.Heights.RestTerms

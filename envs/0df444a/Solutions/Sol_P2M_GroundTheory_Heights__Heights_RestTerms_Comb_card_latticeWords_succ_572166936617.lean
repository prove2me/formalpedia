-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_card_latticeWords_succ_572166936617
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:43:52.107894+00:00
-- url     : https://prove2.me/submissions/5e78734e-ef9d-4893-8f1f-85b40107d932

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Lattice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_castSucc_snoc_2f331b9c4057
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_snoc_last_895168a820dd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_update_pred_sub_9997e7a05bb7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Comb
open MvPolynomial Finset Equiv
noncomputable section
open scoped Classical
variable {m : ℕ}
namespace GroundTheory.Heights₂.Heights.RestTerms.Comb
theorem _root_.solution (n : ℕ) (lam : Fin m → ℕ) (hlam : Antitone lam) :
    (latticeWords (n + 1) lam).card =
      ∑ a : Fin m, if 1 ≤ lam a then (latticeWords n (Function.update lam a (lam a - 1))).card else 0 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun w => w (Fin.last n)) (t := univ)
    (fun _ _ => mem_univ _)]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with ha
  · refine Finset.card_nbij' (fun w => Fin.init w) (fun w => Fin.snoc w a) ?_ ?_ ?_ ?_
    · intro w hw
      simp only [coe_filter, Set.mem_ofPred_eq, latticeWords, mem_filter, mem_univ, true_and] at hw ⊢
      obtain ⟨⟨hlat, hcont⟩, hlast⟩ := hw
      have hw' : w = Fin.snoc (Fin.init w) a := by
        rw [← hlast]; exact (Fin.snoc_init_self w).symm
      refine ⟨fun t ht i j hij => ?_, fun i => ?_⟩
      · have := hlat t (by omega) i j hij
        rwa [hw', pcnt_castSucc_snoc _ _ _ ht, pcnt_castSucc_snoc _ _ _ ht] at this
      · have := hcont i
        rw [hw', pcnt_snoc_last] at this
        have h2 := update_pred_sub lam a i ha
        omega
    · intro w hw
      simp only [coe_filter, Set.mem_ofPred_eq, latticeWords, mem_filter, mem_univ, true_and] at hw ⊢
      obtain ⟨hlat, hcont⟩ := hw
      refine ⟨⟨fun t ht i j hij => ?_, fun i => ?_⟩, by simp⟩
      · rcases Nat.lt_or_ge t (n + 1) with htn | htn
        · rw [pcnt_castSucc_snoc _ _ _ (by omega), pcnt_castSucc_snoc _ _ _ (by omega)]
          exact hlat t (by omega) i j hij
        · have ht' : t = n + 1 := by omega
          subst ht'
          rw [pcnt_snoc_last, pcnt_snoc_last, hcont, hcont, update_pred_sub lam a i ha,
            update_pred_sub lam a j ha]
          exact hlam hij
      · rw [pcnt_snoc_last, hcont, update_pred_sub lam a i ha]
    · intro w hw
      simp only [coe_filter, Set.mem_ofPred_eq] at hw
      rw [← hw.2]; exact Fin.snoc_init_self w
    · intro w hw
      simp
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro w hw hlast
    simp only [latticeWords, mem_filter, mem_univ, true_and] at hw
    have := hw.2 a
    have h1 : 1 ≤ pcnt w (n + 1) a := by
      unfold pcnt
      exact Finset.card_pos.mpr ⟨Fin.last n, by simp [hlast]⟩
    omega
end GroundTheory.Heights₂.Heights.RestTerms.Comb

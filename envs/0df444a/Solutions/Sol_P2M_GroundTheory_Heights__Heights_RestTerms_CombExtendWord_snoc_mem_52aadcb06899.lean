-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CombExtendWord_snoc_mem_52aadcb06899
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:28:13.22269+00:00
-- url     : https://prove2.me/submissions/99a3b1c0-2b08-4b4a-bcb6-5c5566dc3836

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombExtendWord
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Finset Comb
noncomputable section
open scoped Classical
open GroundTheory.Heights₂.Heights.RestTerms.CombExtendWord
namespace GroundTheory.Heights₂.Heights.RestTerms.CombExtendWord
theorem _root_.solution {m n : ℕ} (lam : Fin m → ℕ) (hlam : Antitone lam) (k : Fin m) (hk : 1 ≤ lam k)
    (v : Fin n → Fin m) (hv : v ∈ latticeWords n (Function.update lam k (lam k - 1))) :
    (Fin.snoc v k : Fin (n + 1) → Fin m) ∈ latticeWords (n + 1) lam := by
  simp only [latticeWords, mem_filter, mem_univ, true_and] at hv ⊢
  obtain ⟨hlat, hcont⟩ := hv
  refine ⟨fun t ht i j hij => ?_, fun i => ?_⟩
  · rcases Nat.lt_or_ge t (n + 1) with htn | htn
    · rw [pcnt_castSucc_snoc _ _ _ (by omega), pcnt_castSucc_snoc _ _ _ (by omega)]
      exact hlat t (by omega) i j hij
    · have ht' : t = n + 1 := by omega
      subst ht'
      rw [pcnt_snoc_last, pcnt_snoc_last, hcont, hcont, update_pred_sub lam k i hk,
        update_pred_sub lam k j hk]
      exact hlam hij
  · rw [pcnt_snoc_last, hcont, update_pred_sub lam k i hk]
end GroundTheory.Heights₂.Heights.RestTerms.CombExtendWord

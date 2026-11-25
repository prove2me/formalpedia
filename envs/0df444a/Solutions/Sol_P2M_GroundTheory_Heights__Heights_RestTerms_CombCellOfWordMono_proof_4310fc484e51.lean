-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CombCellOfWordMono_proof_4310fc484e51
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:34:27.699635+00:00
-- url     : https://prove2.me/submissions/500ca894-72aa-445c-b845-79539689fa35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Lattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombCellOfWordMono
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_succ_self_60fc17d3e385
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_le_of_le_fec53aa30c0b


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
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace CombCellOfWordMono
theorem _root_.solution : CombCellOfWordMono.Statement := by
  intro m n w hw s t hrow hcol
  by_contra hst
  rw [not_le] at hst
  simp only [cellOfWord] at hrow hcol
  have h1 : pcnt w ((t : ℕ) + 1) (w t) = pcnt w t (w t) + 1 := Comb.pcnt_succ_self w t
  have h2 : pcnt w ((t : ℕ) + 1) (w s) ≤ pcnt w s (w s) :=
    pcnt_le_of_le w (Nat.succ_le_of_lt hst) (w s)
  have h3 : pcnt w ((t : ℕ) + 1) (w t) ≤ pcnt w ((t : ℕ) + 1) (w s) :=
    hw _ (by have := s.isLt; have : (t : ℕ) < s := hst; omega) (w s) (w t) hrow
  omega
end CombCellOfWordMono
end GroundTheory.Heights₂.Heights.RestTerms

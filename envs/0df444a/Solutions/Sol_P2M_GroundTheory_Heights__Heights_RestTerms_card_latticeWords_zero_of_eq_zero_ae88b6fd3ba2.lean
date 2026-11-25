-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_card_latticeWords_zero_of_eq_zero_ae88b6fd3ba2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:42:57.702222+00:00
-- url     : https://prove2.me/submissions/d6863b0e-181e-4351-93cf-31fd8b83d3e6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Lattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombHookCount

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
theorem _root_.solution {r : ℕ} (lam : Fin r → ℕ) (hlam : ∀ i, lam i = 0) :
    (latticeWords 0 lam).card = 1 := by
  have h : latticeWords 0 lam = univ := by
    ext w
    simp only [latticeWords, mem_filter, mem_univ, true_and, iff_true]
    exact ⟨fun t _ i j _ => by simp [pcnt], fun i => by rw [hlam i]; simp [pcnt]⟩
  rw [h, card_univ]
  simp
end GroundTheory.Heights₂.Heights.RestTerms

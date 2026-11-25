-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_succ_self_60fc17d3e385
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:24:25.103895+00:00
-- url     : https://prove2.me/submissions/1dc1a4f5-8fac-49fc-a482-665214c9adda

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Lattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombCellOfWordMono

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
namespace Comb
theorem _root_.solution {m n : ℕ} (w : Fin n → Fin m) (t : Fin n) :
    pcnt w ((t : ℕ) + 1) (w t) = pcnt w t (w t) + 1 := by
  unfold pcnt
  have hins : (univ.filter (fun s : Fin n => (s : ℕ) < (t : ℕ) + 1 ∧ w s = w t)) =
      insert t (univ.filter (fun s : Fin n => (s : ℕ) < t ∧ w s = w t)) := by
    ext s
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | h
      · exact Or.inr ⟨h, h2⟩
      · exact Or.inl (Fin.ext h)
    · rintro (h | ⟨h1, h2⟩)
      · subst h; exact ⟨Nat.lt_succ_self _, rfl⟩
      · exact ⟨Nat.lt_succ_of_lt h1, h2⟩
  rw [hins, card_insert_of_notMem]
  simp
end Comb
end GroundTheory.Heights₂.Heights.RestTerms

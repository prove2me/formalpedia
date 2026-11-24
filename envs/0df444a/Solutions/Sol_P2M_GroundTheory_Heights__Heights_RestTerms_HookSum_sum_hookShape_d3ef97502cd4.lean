-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_sum_hookShape_d3ef97502cd4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:35.268438+00:00
-- url     : https://prove2.me/submissions/7ad16751-d470-4a09-a438-52bc490c8953

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHookCharacterSumIdentity

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
open GroundTheory.Heights₂.Heights.RestTerms.HookSum
namespace GroundTheory.Heights₂.Heights.RestTerms.HookSum
theorem _root_.solution (r k l : ℕ) (hl : l < r) : ∑ i, hookShape r k l i = (k - l) + l := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [Fin.sum_univ_succ]
  have h0 : hookShape (r' + 1) k l 0 = k - l := by simp [hookShape]
  have hs : ∀ i : Fin r', hookShape (r' + 1) k l i.succ = if (i : ℕ) < l then 1 else 0 := by
    intro i
    simp only [hookShape, Fin.val_succ]
    by_cases h : (i : ℕ) < l
    · rw [if_neg (by omega), if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg (by omega), if_neg h]
  rw [h0]
  simp only [hs]
  congr 1
  rw [Finset.sum_boole]
  have h : (Finset.univ.filter fun i : Fin r' => (i : ℕ) < l) =
      (Finset.range l).attachFin (fun x hx => by rw [Finset.mem_range] at hx; omega) := by
    ext j
    simp [Finset.mem_attachFin]
  rw [h, Finset.card_attachFin, Finset.card_range, Nat.cast_id]
end GroundTheory.Heights₂.Heights.RestTerms.HookSum

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_completeSymmetric_010966416004
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:53:26.907845+00:00
-- url     : https://prove2.me/submissions/9a37504d-6a1a-4826-a3e5-a6da1bf1eeaa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand

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
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution (σ : Type*) [Fintype σ] [DecidableEq σ] (d : ℤ) :
    constantCoeff (completeSymmetric σ d) = if d = 0 then 1 else 0 := by
  unfold completeSymmetric
  split_ifs with h1 h2 h2
  · subst h2; simp [hsymm_zero]
  · have hpos : 0 < d.toNat := by omega
    obtain ⟨n, hn⟩ : ∃ n, d.toNat = n + 1 := ⟨d.toNat - 1, by omega⟩
    rw [hn]
    simp only [hsymm, map_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [map_multiset_prod, Multiset.map_map]
    apply Multiset.prod_eq_zero
    obtain ⟨x, hx⟩ : ∃ x, x ∈ s.1 :=
      Multiset.card_pos_iff_exists_mem.mp (by rw [s.2]; omega)
    exact Multiset.mem_map.mpr ⟨x, hx, by simp⟩
  · omega
  · simp
end GroundTheory.Heights₂.Heights.RestTerms.Top

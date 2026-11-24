-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_rectangle_mem_partitionsOf_35563b48a979
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:47.374946+00:00
-- url     : https://prove2.me/submissions/0a49808a-49e8-4586-a9bc-d9bd467e6967

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
theorem _root_.solution (r a t : ℕ) :
    rectangle r a ∈ partitionsOf r t ↔ t = r * a := by
  simp only [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple, rectangle,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  constructor
  · rintro ⟨h, -⟩; exact h.symm
  · rintro rfl; exact ⟨rfl, fun _ _ _ => le_rfl⟩
end GroundTheory.Heights₂.Heights.RestTerms.Top

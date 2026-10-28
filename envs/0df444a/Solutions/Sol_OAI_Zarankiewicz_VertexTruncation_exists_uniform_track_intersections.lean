-- Prove2me | solution 1 for OAI.Zarankiewicz.VertexTruncation.exists_uniform_track_intersections
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T13:20:09.324873+00:00
-- url     : https://prove2.me/submissions/aa9e98bf-8888-4963-9c14-6b450ee7bf47

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_BipartiteCrossing
import Definitions.Def_OAIB3Zr002
import Theorems.Thm_OAI_Zarankiewicz_VertexTruncation_exists_all_edge_shift_radius

section
-- module Solutions.OAIB3_Zar.Crossing_UniformTrackPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.VertexTruncation
open scoped BigOperators
variable {m n : ℕ} {D : AdmissibleDrawing m n}

theorem exists_uniform_track_intersections_oai (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, t ≠ 0 → |t| < δ → ∀ e f : BipartiteEdge m n,
      polygonIntersection (V.vertices e) (shiftedTrack (V.vertices f) (V.pieces f) t) (V.pieces e) (V.pieces f) =
        if e=f then 0 else polygonIntersection (V.vertices e) (V.vertices f) (V.pieces e) (V.pieces f) := by
  classical
  obtain ⟨δ,hδ,hh⟩ := V.exists_all_edge_shift_radius hnorm hstraight htrans
  refine ⟨δ,hδ,?_⟩
  intro t ht hsmall e f
  by_cases hef : e=f
  · rw [ite_eq_left hef]
    unfold polygonIntersection
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    simpa only [ite_eq_left hef] using
      (hh t ht hsmall e f ⟨i,Finset.mem_range.mp hi⟩ ⟨j,Finset.mem_range.mp hj⟩).2
  · rw [ite_eq_right hef]
    unfold polygonIntersection
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [ite_eq_right hef] using
      (hh t ht hsmall e f ⟨i,Finset.mem_range.mp hi⟩ ⟨j,Finset.mem_range.mp hj⟩).2

end Zarankiewicz.VertexTruncation

end

end OAI
end

theorem solution : type_of% @OAI.Zarankiewicz.VertexTruncation.exists_uniform_track_intersections_oai := @OAI.Zarankiewicz.VertexTruncation.exists_uniform_track_intersections_oai

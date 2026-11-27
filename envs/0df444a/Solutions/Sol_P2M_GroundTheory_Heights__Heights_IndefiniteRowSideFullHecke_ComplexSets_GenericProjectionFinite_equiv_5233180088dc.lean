-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GenericProjectionFinite_equiv_5233180088dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:57:05.289834+00:00
-- url     : https://prove2.me/submissions/c750a0c9-c2d5-433e-9bb4-30b742bb2a40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_IsClosedComplexSubmanifoldIn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ProjDegreeEqFinrankAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ImportsAlt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_Objects_isFiniteProjection_iff_6a65007f0610
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_Objects_orthoRows_eq_3882db7d1ef6


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Matrix
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace GenericProjectionFinite
theorem _root_.solution :
    GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GenericProjectionFinite.Statement := by
  unfold GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.Statement
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GenericProjectionFinite.Statement
  refine forall_congr' fun n => forall_congr' fun d => forall_congr' fun J =>
    imp_congr_right fun _ => imp_congr_right fun _ => ?_
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · constructor
    · rintro ⟨U, ⟨S, rfl⟩, ⟨A, hA⟩, hU⟩
      exact ⟨S, ⟨A, hA⟩, fun M hM => (Objects.isFiniteProjection_iff J M).mp (hU M hM)⟩
    · rintro ⟨S, ⟨A, hA⟩, hS⟩
      exact ⟨{M | ∃ f ∈ S, eval (fun p : Fin d × Fin n => M p.1 p.2) f ≠ 0}, ⟨S, rfl⟩, ⟨A, hA⟩,
        fun M hM => (Objects.isFiniteProjection_iff J M).mpr (hS M hM)⟩
  · simp only [Set.Nonempty, Set.mem_ofPred_eq, Objects.isFiniteProjection_iff]
  · simp only [Objects.orthoRows_eq, Objects.isFiniteProjection_iff]
  · constructor
    · intro h m F hF
      obtain ⟨U, hU, hk⟩ := h m fun k => ⟨(F k)ᴴ, by
        simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem (hF k)⟩
      refine ⟨Uᴴ, by simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem hU,
        fun k s => ?_⟩
      rw [← Objects.isFiniteProjection_iff]
      simpa [Matrix.conjTranspose_mul] using hk k s
    · intro h m F
      obtain ⟨U, hU, hk⟩ := h m (fun k => (F k : Matrix (Fin n) (Fin n) ℂ)ᴴ) fun k => by
        simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem (F k).2
      refine ⟨Uᴴ, by simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem hU,
        fun k s => ?_⟩
      rw [Objects.isFiniteProjection_iff]
      simpa [Matrix.conjTranspose_mul] using hk k s
end GenericProjectionFinite
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

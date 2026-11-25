-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_colon_span_singleton_eq_of_not_mem_585d56ee6b6a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:56:55.774482+00:00
-- url     : https://prove2.me/submissions/d9c723d2-65c2-471a-bbd6-1786497ab602

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ProjectiveSpaceIncrementHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ColonSpanSingletonEqOfNotMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
theorem _root_.solution {R : Type*} [CommRing R] {q : Ideal R} [q.IsPrime]
    {s : R} (hs : s ∉ q) : q.colon (Ideal.span {s}) = q := by
  ext x
  rw [Submodule.mem_colon_span_singleton, smul_eq_mul]
  constructor
  · intro h
    exact (Ideal.IsPrime.mem_or_mem inferInstance h).resolve_right hs
  · intro h
    exact q.mul_mem_right _ h
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

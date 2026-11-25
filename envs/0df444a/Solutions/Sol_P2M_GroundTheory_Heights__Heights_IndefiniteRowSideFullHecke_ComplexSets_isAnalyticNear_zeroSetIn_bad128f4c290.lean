-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isAnalyticNear_zeroSetIn_bad128f4c290
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:33:09.687412+00:00
-- url     : https://prove2.me/submissions/439d69fa-57c7-4eb9-a005-2521ecbae145

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalZerosNowhereDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalGermIntegrallyClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermRegularConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularLocusDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalZerosNowhereDense

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
open MvPolynomial Topology Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) :
    IsAnalyticNear (zeroSetIn I) w := by
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
  refine ⟨Set.univ, s.card, fun i z => eval z (s.equivFin.symm i : MvPolynomial σ ℂ), isOpen_univ, trivial,
    fun i => AnalyticOnNhd.eval_mvPolynomial _, ?_⟩
  ext z
  simp only [Set.mem_inter_iff, Set.mem_univ, and_true, Set.mem_ofPred_eq, true_and]
  constructor
  · intro hz i
    apply hz
    rw [← hs]
    exact Submodule.subset_span (s.equivFin.symm i).2
  · intro hz q hq
    have hle : Ideal.span (s : Set (MvPolynomial σ ℂ)) ≤ RingHom.ker (MvPolynomial.eval z) := by
      rw [Ideal.span_le]
      intro p hp
      rw [SetLike.mem_coe, RingHom.mem_ker]
      simpa using hz (s.equivFin ⟨p, hp⟩)
    rw [← hs] at hq
    exact hle hq
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

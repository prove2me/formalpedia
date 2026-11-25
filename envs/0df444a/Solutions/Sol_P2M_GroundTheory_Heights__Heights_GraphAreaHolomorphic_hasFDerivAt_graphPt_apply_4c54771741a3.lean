-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_hasFDerivAt_graphPt_apply_4c54771741a3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:54:28.315654+00:00
-- url     : https://prove2.me/submissions/c633fc0a-3cea-4ac5-bbcd-e9567282bf39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGraphAreaHolomorphic
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGraphAreaHolomorphic

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
open MeasureTheory Module
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.GraphAreaHolomorphic
namespace GroundTheory.Heights₂.Heights.GraphAreaHolomorphic
theorem _root_.solution {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    {F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)} {x : EuclideanSpace ℂ (Fin d)}
    {L : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin m)} (hF : HasFDerivAt F L x)
    {T : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin n)} (hG : HasFDerivAt (graphPt e F) T x)
    (v : EuclideanSpace ℂ (Fin d)) :
    T v = WithLp.toLp 2 (fun j => Sum.elim (fun i => v i) (fun i => L v i) (e j)) := by
  ext j
  obtain ⟨s, rfl⟩ := e.symm.surjective j
  have hj := (hasFDerivWithinAt_piLp 2).1 (hasFDerivWithinAt_univ.2 hG) (e.symm s)
  rw [hasFDerivWithinAt_univ] at hj
  rcases s with i | i
  · have h' : HasFDerivAt (fun y : EuclideanSpace ℂ (Fin d) => graphPt e F y (e.symm (Sum.inl i)))
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℂ) i) x := by
      simpa [graphPt] using PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x i
    simpa using congrArg (fun M => M v) (hj.unique h')
  · have hfun : (fun y : EuclideanSpace ℂ (Fin d) => graphPt e F y (e.symm (Sum.inr i))) =
        (fun f : EuclideanSpace ℂ (Fin m) => f i) ∘ F := by
      funext y
      simp [graphPt]
    have h' : HasFDerivAt (fun y : EuclideanSpace ℂ (Fin d) => graphPt e F y (e.symm (Sum.inr i)))
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℂ) i).comp L) x := by
      rw [hfun]
      exact (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (F x) i).comp x hF
    simpa using congrArg (fun M => M v) (hj.unique h')
end GroundTheory.Heights₂.Heights.GraphAreaHolomorphic

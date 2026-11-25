-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_OsgoodSeparate_cons_mem_ball_309c0470889e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:56:56.002963+00:00
-- url     : https://prove2.me/submissions/2acbb4da-b32e-481a-9701-3ef6b149df5b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PRiemannExtensionSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_mem_ball_pi_iff


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
open Complex Metric MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.Osgood
  GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.OsgoodSeparate
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.OsgoodSeparate
theorem _root_.solution {n : ℕ} {c : Fin (n + 1) → ℂ} {R : ℝ} {x : ℂ} (hx : x ∈ ball (c 0) R)
    {y : Fin n → ℂ} (hy : y ∈ ball (Fin.tail c) R) : (Fin.cons x y : Fin (n + 1) → ℂ) ∈ ball c R := by
  have hR : 0 < R := pos_of_mem_ball hx
  refine (mem_ball_pi_iff hR).mpr fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hx
  · simpa [Fin.tail] using (mem_ball_pi_iff hR).mp hy j
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.OsgoodSeparate

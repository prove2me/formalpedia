-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicOnSubset_differentiableAt_comp_a8c1a300de3d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:09.341886+00:00
-- url     : https://prove2.me/submissions/2c7ce01d-4d66-481e-9778-36205fa545d6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalTrace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalBranchedCovering
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalTrace

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
namespace HolomorphicOnSubset
theorem _root_.solution {σ : Type*} [Fintype σ] {k : ℕ}
    {g : (σ → ℂ) → ℂ} {S : Set (σ → ℂ)} (hg : HolomorphicOnSubset g S)
    {s : (Fin k → ℂ) → σ → ℂ} {y : Fin k → ℂ} (hs : DifferentiableAt ℂ s y)
    (hS : ∀ᶠ y' in 𝓝 y, s y' ∈ S) : DifferentiableAt ℂ (fun y' => g (s y')) y := by
  obtain ⟨V, hV, hzV, F, hF, hgF⟩ := hg (s y) hS.self_of_nhds
  have hFd : DifferentiableAt ℂ F (s y) := hF.differentiableAt (hV.mem_nhds hzV)
  have hev : ∀ᶠ y' in 𝓝 y, s y' ∈ V := hs.continuousAt.preimage_mem_nhds (hV.mem_nhds hzV)
  refine (hFd.comp y hs).congr_of_eventuallyEq ?_
  filter_upwards [hS, hev] with y' h1 h2 using hgF ⟨h1, h2⟩
end HolomorphicOnSubset
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_gramDet_sub_994da6b3e634
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:36:37.93144+00:00
-- url     : https://prove2.me/submissions/473b63ea-7fd8-45a2-ad39-59fe4b602826

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSublattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField GroundTheory.Heights₂.Heights
noncomputable section
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
theorem _root_.solution {K : Type*} [Field K] [NumberField K] (M : HermitianBundle K)
    (F : Submodule (𝓞 K) M.carrier) (σ : K →+* ℂ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → F) :
    gramDet (M.sub F).metric σ s = gramDet M.metric σ (fun i ↦ (s i : M.carrier)) := by
  have hG : (Matrix.gram ℂ fun i ↦ fibreVec (M.sub F).metric σ (s i)) =
      Matrix.gram ℂ fun i ↦ fibreVec M.metric σ (s i : M.carrier) := by
    ext i j
    rfl
  simp only [gramDet]
  rw [hG]
end GroundTheory.Heights₂.Heights.LatticeLemmas

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootAnchorNonzero_proof_c9d850c3c7df
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:08:58.373939+00:00
-- url     : https://prove2.me/submissions/ec017036-4baf-4678-9baf-ca35c9aa481b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootAnchorNonzero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootAnchorNonzeroAlt_rootCoord_isIntegral_77b0fc8c9165
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootAnchorNonzeroAlt_homForm_mem_eb6e66a4f8a1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootAnchorNonzeroAlt_eval_homForm_698e79acdc72

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace RootAnchorNonzero
theorem _root_.solution : RootAnchorNonzero.Statement := by
  intro f j m ζ hζ z hz τ h0
  obtain ⟨I, hI⟩ := hz.1 τ
  obtain ⟨q, hqm, hq⟩ := RootAnchorNonzeroAlt.rootCoord_isIntegral hζ ⟨τ, I⟩
  have hmem := RootAnchorNonzeroAlt.homForm_mem ζ q τ I (by rwa [Polynomial.aeval_def])
  have h := hz.2 _ hmem
  rw [RootAnchorNonzeroAlt.eval_homForm hqm h0] at h
  exact hI (pow_eq_zero_iff'.mp h).1
end RootAnchorNonzero
end GroundTheory.Heights₂.Heights

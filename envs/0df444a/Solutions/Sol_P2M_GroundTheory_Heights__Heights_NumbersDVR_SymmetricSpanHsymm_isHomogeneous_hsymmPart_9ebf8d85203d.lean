-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_isHomogeneous_hsymmPart_9ebf8d85203d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:22:39.646494+00:00
-- url     : https://prove2.me/submissions/666be72c-ad16-4705-bd61-1217508e82df

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Capelli_CompleteHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSymmetricSpanHsymm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_isHomogeneous_prod_map_hsymm_55f0349fa572

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial Finset
open GroundTheory.Heights₂.Heights.NumbersDVR.SymmetricSpanHsymm
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.SymmetricSpanHsymm
theorem _root_.solution {n : ℕ} (μ : n.Partition) : (hsymmPart σ ℤ μ).IsHomogeneous n := by
  have := isHomogeneous_prod_map_hsymm (σ := σ) μ.parts
  rwa [μ.parts_sum] at this
end GroundTheory.Heights₂.Heights.NumbersDVR.SymmetricSpanHsymm

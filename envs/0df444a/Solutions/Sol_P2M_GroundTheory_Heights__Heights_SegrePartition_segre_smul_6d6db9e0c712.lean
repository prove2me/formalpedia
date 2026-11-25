-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SegrePartition_segre_smul_6d6db9e0c712
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:16:37.99414+00:00
-- url     : https://prove2.me/submissions/734d8ee2-3040-468c-94be-60ca9f65cdfe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegrePartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegrePartition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo (segre)
open GroundTheory.Heights₂.Heights.SegrePartition
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [DecidableEq K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.SegrePartition
theorem _root_.solution (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (i : (k : K) → ι k) :
    segre (fun p => c p.1 * z p) i = (∏ k, c k) * segre z i :=
  Finset.prod_mul_distrib
end GroundTheory.Heights₂.Heights.SegrePartition

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_rename_psumExpansion_d622675f0759
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:44:41.184199+00:00
-- url     : https://prove2.me/submissions/4bd45ddf-1a43-4076-b85e-38513b005693

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSubQuotient

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {M N : ℕ} (e : Fin M → Fin N) (k : ℕ) (i : Fin M) :
    rename (Sum.map e e) (psumExpansion M k i) = psumExpansion N k (e i) := by
  simp [psumExpansion, map_sum, rename_X]
end GroundTheory.Heights₂.Heights.NumbersDVR

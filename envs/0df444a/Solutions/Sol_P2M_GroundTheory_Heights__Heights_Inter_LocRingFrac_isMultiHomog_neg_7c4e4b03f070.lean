-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_LocRingFrac_isMultiHomog_neg_7c4e4b03f070
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:56:55.806016+00:00
-- url     : https://prove2.me/submissions/5e62145f-2283-429b-a8f0-f6a3b2a405b9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingFrac

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.LocRingFrac
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.LocRingFrac
theorem _root_.solution {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm k
  rw [MvPolynomial.support_neg] at hm
  exact hf m hm k
end GroundTheory.Heights₂.Heights.Inter.LocRingFrac

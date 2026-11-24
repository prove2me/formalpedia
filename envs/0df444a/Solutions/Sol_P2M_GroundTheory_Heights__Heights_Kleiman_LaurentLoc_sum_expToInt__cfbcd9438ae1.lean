-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_sum_expToInt__cfbcd9438ae1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:02:54.53953+00:00
-- url     : https://prove2.me/submissions/9e873f4c-969f-4c96-bbcb-4a36d03c29cb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
variable {S : Type u} [CommRing S] {N : ℕ}
attribute [local instance] algP
namespace GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
theorem _root_.solution (d : Fin (N + 1) →₀ ℕ) :
    ∑ j, expToInt N d j = ((Finsupp.weight (1 : Fin (N + 1) → ℕ) d : ℕ) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [expToInt]
end GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc

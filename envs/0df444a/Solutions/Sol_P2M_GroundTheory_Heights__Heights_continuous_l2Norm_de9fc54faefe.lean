-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_continuous_l2Norm_de9fc54faefe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:55.830213+00:00
-- url     : https://prove2.me/submissions/568357ec-441b-4beb-b00a-c8a1ae6bcfd0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison

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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {m : ℕ} : Continuous (fun w : Fin m → ℂ ↦ l2Norm w) :=
  Real.continuous_sqrt.comp
    (continuous_finsetSum _ fun i _ ↦ (continuous_norm.comp (continuous_apply i)).pow 2)
end GroundTheory.Heights₂.Heights

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_oneBlockForms_symm_apply_3b06e6409374
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:42.278522+00:00
-- url     : https://prove2.me/submissions/cbc155e5-faca-40b3-ad14-bede1c4fd0e6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockStandard

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
open MvPolynomial NumberField Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
omit [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {e r : ℕ} (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K))
    (a : Fin (e + 1)) (j : Fin (r + 1)) :
    oneBlockForms om ((oneBlockIndex e r).symm (a, j)) = Pi.single j ((om a : 𝓞 K) : K) := by
  simp [oneBlockForms]
end GroundTheory.Heights₂.Heights

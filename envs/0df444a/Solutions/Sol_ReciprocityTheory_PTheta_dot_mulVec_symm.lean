-- Prove2me | solution 1 for ReciprocityTheory.PTheta.dot_mulVec_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:53.761803+00:00
-- url     : https://prove2.me/submissions/9dd27659-4edd-4400-8947-b18590017d36

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
open ReciprocityTheory ReciprocityTheory.PTheta
variable {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.PTheta
theorem _root_.solution {τ : Matrix ι ι ℂ} (hτ : τ.IsSymm) (s w : ι → ℂ) :
    w ⬝ᵥ (τ *ᵥ s) = s ⬝ᵥ (τ *ᵥ w) := by
  rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hτ.eq]
end ReciprocityTheory.PTheta

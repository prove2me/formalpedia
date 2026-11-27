-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_blockForms_not_mem_3c0f34b00d5e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:10:33.712853+00:00
-- url     : https://prove2.me/submissions/5a293088-3b3c-4c27-9027-3e22a89cf1ed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_blockSubst_eq_zero_584f1638d3d0

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
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (n : ι → ℕ) (k₀ : ι)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (c : (k : ι) → Fin (n k + 1)) (j : Fin ((blockAddData n k₀).size + 1)) :
    (blockAddData n k₀).liftOld (blockForms n k₀ c j) ∉ (blockAddData n k₀).extIdeal := by
  intro h
  have h2 := blockSubst_eq_zero n k₀ h
  simp [blockForms, chartMonomial, AddBlockData.liftOld, AddBlockData.oldCoord, blockSubst, blockVal,
    Finset.prod_eq_zero_iff, X_ne_zero] at h2
end GroundTheory.Heights₂.Heights

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockSurjectivity_atBlock_apply_5df1ecab43d1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:03:12.9312+00:00
-- url     : https://prove2.me/submissions/9299e08b-89fa-4992-a078-f8af49b42ae4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousSepBlock

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
open MvPolynomial Module
noncomputable section
open GroundTheory.Heights₂.Heights.BlockSurjectivity
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.BlockSurjectivity
theorem _root_.solution (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ) (q : MvPolynomial (Coord n) ℤ) :
    atBlock k₀ w q = map (evalBlock w) (sepBlock k₀ q) := rfl
end GroundTheory.Heights₂.Heights.BlockSurjectivity

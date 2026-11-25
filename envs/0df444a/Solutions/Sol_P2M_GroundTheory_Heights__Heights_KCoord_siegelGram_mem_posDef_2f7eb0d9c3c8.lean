-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KCoord_siegelGram_mem_posDef_2f7eb0d9c3c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:37:08.190797+00:00
-- url     : https://prove2.me/submissions/d35cfe7f-e548-41c3-b0ed-fddb6a0b8085

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_CoordSiegel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KCoord_posDef_fromBlocks_diag_ca156480bfd5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KCoord_siegelGram_eq_e89b1c54405c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KCoord_unip_mem_d70ea5258c05
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KCoord_diagInv_mem_ff8cc4ad4488
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KCoord_unip_isUnit_17db654cb6d4

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
open Matrix
variable {g : ℕ}
open GroundTheory.Heights₂.Heights.KCoord
namespace GroundTheory.Heights₂.Heights.KCoord
theorem _root_.solution (X Y : Matrix (Fin g) (Fin g) ℝ) (hX : X.IsSymm) (hY : Y.PosDef) :
    siegelGram X Y ∈ symplecticGroup (Fin g) ℝ ∧ (siegelGram X Y).PosDef := by
  rw [siegelGram_eq X Y hX]
  refine ⟨Submonoid.mul_mem _ (Submonoid.mul_mem _
    (SymplecticGroup.transpose_mem (unip_mem X hX)) (diagInv_mem Y hY)) (unip_mem X hX), ?_⟩
  have hD : (diagInv Y).PosDef := posDef_fromBlocks_diag hY.inv hY
  have hinj : Function.Injective (unip X).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr (unip_isUnit X)
  have := hD.conjTranspose_mul_mul_same hinj
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
end GroundTheory.Heights₂.Heights.KCoord

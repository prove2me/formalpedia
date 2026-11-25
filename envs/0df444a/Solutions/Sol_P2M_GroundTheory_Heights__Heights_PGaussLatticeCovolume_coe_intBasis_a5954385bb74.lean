-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PGaussLatticeCovolume_coe_intBasis_a5954385bb74
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:45:43.875696+00:00
-- url     : https://prove2.me/submissions/b3c6c198-5645-4797-aa77-d801f8a5c5ed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussLatticeCovolume

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
open Matrix MeasureTheory Module
noncomputable section
open GroundTheory.Heights₂.Heights.PGaussLatticeCovolume
namespace GroundTheory.Heights₂.Heights.PGaussLatticeCovolume
theorem _root_.solution {g : ℕ} {B : Matrix (Fin g) (Fin g) ℝ} (hB : B.det ≠ 0) :
    ((↑) : gaussLattice B → EuclideanSpace ℝ (Fin g)) ∘ intBasis hB = cols B := by
  funext i
  simp [intBasis, Basis.restrictScalars_apply, coe_colBasis]
end GroundTheory.Heights₂.Heights.PGaussLatticeCovolume

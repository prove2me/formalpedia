-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PGaussLatticeIsLattice_gaussLattice_eq_span_87f11a2bad57
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:51.128455+00:00
-- url     : https://prove2.me/submissions/9eb1da09-6d73-4cb9-b9fa-ba134caeb82f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussLatticeIsLattice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussLatticeIsLattice_colBasis_apply_4a639237e26c

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
noncomputable section
open GroundTheory.Heights₂.Heights.PGaussLatticeIsLattice
namespace GroundTheory.Heights₂.Heights.PGaussLatticeIsLattice
theorem _root_.solution {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0) :
    gaussLattice B = Submodule.span ℤ (Set.range (colBasis B hB)) := by
  unfold gaussLattice
  congr 2
  funext i
  exact (colBasis_apply B hB i).symm
end GroundTheory.Heights₂.Heights.PGaussLatticeIsLattice

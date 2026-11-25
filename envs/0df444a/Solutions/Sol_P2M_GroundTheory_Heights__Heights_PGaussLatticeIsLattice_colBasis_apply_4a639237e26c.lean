-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PGaussLatticeIsLattice_colBasis_apply_4a639237e26c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:45:50.233884+00:00
-- url     : https://prove2.me/submissions/d0e2232c-bc1f-4063-b434-90616ba6a095

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussLatticeIsLattice

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
theorem _root_.solution {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0) (i : Fin g) :
    colBasis B hB i = WithLp.toLp 2 (B *ᵥ Pi.single i 1) := by
  rw [colBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  rfl
end GroundTheory.Heights₂.Heights.PGaussLatticeIsLattice

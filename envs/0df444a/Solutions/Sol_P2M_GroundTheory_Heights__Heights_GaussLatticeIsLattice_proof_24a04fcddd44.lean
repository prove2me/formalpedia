-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GaussLatticeIsLattice_proof_24a04fcddd44
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:54:46.620388+00:00
-- url     : https://prove2.me/submissions/9dc26c7c-6508-452a-97f0-829fca3967c9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussLatticeIsLattice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussLatticeIsLattice_gaussLattice_eq_span_87f11a2bad57

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
open PGaussLatticeIsLattice
namespace GroundTheory.Heights₂.Heights
namespace GaussLatticeIsLattice
theorem _root_.solution : GaussLatticeIsLattice.Statement := by
  intro g B hB
  have h := gaussLattice_eq_span B hB
  refine ⟨?_, fun {_} => ⟨?_⟩⟩
  · rw [h]; infer_instance
  · rw [h]; exact ZSpan.span_top (colBasis B hB)
end GaussLatticeIsLattice
end GroundTheory.Heights₂.Heights

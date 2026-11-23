-- Prove2me | solution 1 for P2M_Formalism_F_covol_pos__b55c804d1109
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:28:45.397066+00:00
-- url     : https://prove2.me/submissions/fed4843f-8116-4d0a-bf26-e1c76c9b271b

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolPos
import Theorems.Thm_Formalism_F_linearIndependent_coe_basis
import Theorems.Thm_Formalism_F_covol_eq_gram


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.F
namespace Formalism.F
theorem _root_.solution : CovolPos := by
  intro E _ _ _ L hL
  haveI := hL
  rw [covol_eq_gram E L (Fin (Module.finrank ℤ L)) (Module.finBasis ℤ L)]
  apply Real.sqrt_pos.2
  exact (Matrix.posDef_gram_of_linearIndependent (linearIndependent_coe_basis L _)).det_pos
end Formalism.F

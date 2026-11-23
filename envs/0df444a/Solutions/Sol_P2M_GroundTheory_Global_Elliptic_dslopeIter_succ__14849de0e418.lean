-- Prove2me | solution 1 for P2M_GroundTheory_Global_Elliptic_dslopeIter_succ__14849de0e418
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:22.56069+00:00
-- url     : https://prove2.me/submissions/1bb9df3d-04aa-4022-8e84-75513896d808

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution (p : ℂ) (k : ℕ) (g : ℂ → ℂ) :
    dslopeIter p (k + 1) g = Function.swap dslope p (dslopeIter p k g) :=
  Function.iterate_succ_apply' _ _ _
end GroundTheory.Global.Elliptic

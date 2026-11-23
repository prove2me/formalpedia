-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:57.95968+00:00
-- url     : https://prove2.me/submissions/6b56b15b-d3cb-4de4-bd0e-d6d97a5cc0d8

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_CoeGalRootsOfUnityHomApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
universe w u v
variable (K : Type*) (L : Type u) [Field K] [Field L] [Algebra K L]
variable {K L}
namespace GroundTheory.ProfCoh
theorem _root_.solution (σ : Gal(L/K)) (x : L) : (galAddInt.{w} K L).ρ σ x = σ x :=
  rfl
end GroundTheory.ProfCoh

-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:58.233838+00:00
-- url     : https://prove2.me/submissions/324aa43b-03fa-4521-a86c-018b78183b61

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
theorem _root_.solution (σ : Gal(L/K)) (x : L) : (galAdd K L).ρ σ x = σ x :=
  rfl
end GroundTheory.ProfCoh

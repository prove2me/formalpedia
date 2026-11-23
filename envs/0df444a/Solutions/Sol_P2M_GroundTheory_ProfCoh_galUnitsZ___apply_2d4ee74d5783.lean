-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:46.330471+00:00
-- url     : https://prove2.me/submissions/cd00c2de-65a2-4d20-958c-e1d20b080d20

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
theorem _root_.solution (σ : Gal(L/K)) (x : Additive Lˣ) :
    (galUnitsZ K L).ρ σ x = Additive.ofMul (galUnitsHom K L σ x.toMul) :=
  rfl
end GroundTheory.ProfCoh

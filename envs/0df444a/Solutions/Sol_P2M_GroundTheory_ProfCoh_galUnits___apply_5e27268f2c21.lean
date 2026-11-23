-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:52.41786+00:00
-- url     : https://prove2.me/submissions/dd45c2b9-911c-42a8-a9e9-130d0547beb7

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
    (galUnits.{w} K L).ρ σ x = Additive.ofMul (galUnitsHom K L σ x.toMul) :=
  rfl
end GroundTheory.ProfCoh

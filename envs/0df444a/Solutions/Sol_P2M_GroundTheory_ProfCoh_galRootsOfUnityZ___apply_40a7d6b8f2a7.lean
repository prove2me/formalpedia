-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:46.149748+00:00
-- url     : https://prove2.me/submissions/51b68d30-6855-4d48-b711-9c38cf7680e2

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
theorem _root_.solution (n : ℕ) (σ : Gal(L/K)) (x : Additive (rootsOfUnity n L)) :
    (galRootsOfUnityZ K L n).ρ σ x = Additive.ofMul (galRootsOfUnityHom K L n σ x.toMul) :=
  rfl
end GroundTheory.ProfCoh

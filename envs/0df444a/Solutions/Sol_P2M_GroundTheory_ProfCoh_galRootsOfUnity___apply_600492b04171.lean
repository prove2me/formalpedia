-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:46.322673+00:00
-- url     : https://prove2.me/submissions/f14588fd-bc69-4f68-9ccd-763c61964562

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
    (galRootsOfUnity.{w} K L n).ρ σ x = Additive.ofMul (galRootsOfUnityHom K L n σ x.toMul) :=
  rfl
end GroundTheory.ProfCoh

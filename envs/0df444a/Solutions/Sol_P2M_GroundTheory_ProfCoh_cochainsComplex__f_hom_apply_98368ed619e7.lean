-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_cochainsComplex__f_hom_apply_98368ed619e7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:12:54.362378+00:00
-- url     : https://prove2.me/submissions/3c122bf6-81b4-44aa-b51e-67deb55e1925

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules_IsDiscreteRepIffForallExistsOpenNormalSubgroup
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]
variable [IsTopologicalGroup G]
namespace GroundTheory.ProfCoh
theorem _root_.solution (A : Rep.{u} k G) [IsDiscreteRep A] (n : ℕ)
    (f : locallyConstantCochains A n) :
    ((cochainsComplexι A).f n).hom f = (f : (Fin n → G) → A) :=
  rfl
end GroundTheory.ProfCoh

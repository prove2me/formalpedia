-- Prove2me | solution 1 for UpperTheory.V.Alg.Lift.map_hom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:15.774983+00:00
-- url     : https://prove2.me/submissions/dd7e6291-bc2a-442b-adf4-4f535752574e

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CommutativeAlgebra_ResMapBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing MvPowerSeries
open UpperTheory UpperTheory.V UpperTheory.V.Alg
attribute [instance] IsCO.complete IsCO.isLocalHom
attribute [instance] WPres.fin
variable (O : Type) [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [Fintype ι]
  [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O))
variable {O rbar} {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R']
namespace UpperTheory.V.Alg
namespace Lift
theorem _root_.solution (f : R →ₐ[O] R') (r : Lift O rbar R) (g : Γ) (a b : ι) :
    (r.map f).hom g a b = f (r.hom g a b) := rfl
end Lift
end UpperTheory.V.Alg

-- Prove2me | solution 1 for UpperTheory.V.Hi.IsCNL.ofCO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:35:27.105131+00:00
-- url     : https://prove2.me/submissions/e930666d-1c52-4eef-b0b8-43537b8d93c4

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_HeckeAlgebras_ContinuousTorusCharacter
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CommutativeAlgebra_ResMapBijective
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_HeckeAlgebras_HeckeCommRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing
open UpperTheory UpperTheory.V UpperTheory.V.Hi
variable {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M]
namespace UpperTheory.V.Hi
namespace IsCNL
theorem _root_.solution (O R : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CommRing R] [Algebra O R]
    [Alg.IsCO O R] : IsCNL R where
  complete := inferInstance
  finite := Finite.of_surjective _ (Alg.resMap_bijective O R).2
end IsCNL
end UpperTheory.V.Hi

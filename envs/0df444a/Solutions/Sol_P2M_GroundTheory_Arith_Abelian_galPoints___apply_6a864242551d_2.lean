-- Prove2me | solution 2 for P2M_GroundTheory_Arith_Abelian_galPoints___apply_6a864242551d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:53:24.628467+00:00
-- url     : https://prove2.me/submissions/31b4e25d-3e25-4a79-ae0e-70b401918e01

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Torsion
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TorsionGalois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open GroundTheory.ProfCoh IntermediateField AddSubgroup WeierstrassCurve
universe w u
variable (K L : Type u) [Field K] [Field L] [Algebra K L] [DecidableEq L] (W : WeierstrassCurve K)
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (σ : Gal(L/K)) (P : (W.baseChange L).toAffine.Point) :
    (galPoints.{w} K L W).ρ σ P = galPointsHom K L W σ P :=
  rfl
end GroundTheory.Arith.Abelian

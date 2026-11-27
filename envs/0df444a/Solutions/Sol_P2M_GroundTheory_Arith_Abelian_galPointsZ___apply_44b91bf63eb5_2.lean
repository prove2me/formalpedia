-- Prove2me | solution 2 for P2M_GroundTheory_Arith_Abelian_galPointsZ___apply_44b91bf63eb5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:53:19.638815+00:00
-- url     : https://prove2.me/submissions/3db80daf-7803-45aa-bb62-1dedf7b6e0ea

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
    (galPointsZ K L W).ρ σ P = galPointsHom K L W σ P :=
  rfl
end GroundTheory.Arith.Abelian

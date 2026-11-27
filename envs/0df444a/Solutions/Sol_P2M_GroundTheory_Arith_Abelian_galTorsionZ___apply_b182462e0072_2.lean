-- Prove2me | solution 2 for P2M_GroundTheory_Arith_Abelian_galTorsionZ___apply_b182462e0072
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:53:29.071508+00:00
-- url     : https://prove2.me/submissions/0381a696-3b7f-4283-91df-c77cd9d6f3c6

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
theorem _root_.solution (n : ℕ) (σ : Gal(L/K))
    (P : torsionBy (W.baseChange L).toAffine.Point n) :
    (galTorsionZ K L W n).ρ σ P = galTorsionHom K L W n σ P :=
  rfl
end GroundTheory.Arith.Abelian

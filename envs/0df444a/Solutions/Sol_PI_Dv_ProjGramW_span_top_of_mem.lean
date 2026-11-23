-- Prove2me | solution 1 for PI.Dv.ProjGramW.span_top_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:22.397504+00:00
-- url     : https://prove2.me/submissions/9076be98-86d7-417b-8f33-f2c737a3b35f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjGramW
theorem _root_.solution {Z : Submodule (𝓞 K) K} {z : K} (hz : z ∈ Z) (hz0 : z ≠ 0) :
    Submodule.span K (Z : Set K) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Submodule.subset_span hz) (isUnit_iff_ne_zero.mpr hz0)
end PI.Dv.ProjGramW

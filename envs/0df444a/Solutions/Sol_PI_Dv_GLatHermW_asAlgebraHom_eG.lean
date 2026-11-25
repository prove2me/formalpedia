-- Prove2me | solution 1 for PI.Dv.GLatHermW.asAlgebraHom_eG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:39:57.1104+00:00
-- url     : https://prove2.me/submissions/3d8b1a18-b6d5-4c7a-aa4e-3a03ecf458ee

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_StarMapTraceOfPowEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_AsAlgebraHomEG
import Theorems.Thm_PI_Dv_GLatHermW_eG_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLatHermW
open PI.Dv
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.GLatHermW
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] (T : GoodSet K G)
    (ρ : Representation K G V) : ρ.asAlgebraHom (eG T) = ∑ g : G, cf T g • ρ g := by
  rw [eG_eq, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, Representation.asAlgebraHom_of]
end PI.Dv.GLatHermW

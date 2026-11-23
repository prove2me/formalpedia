-- Prove2me | solution 1 for PI.Dv.GLP.asAlg_eS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:17.219488+00:00
-- url     : https://prove2.me/submissions/2786d75e-00fc-49d2-a93f-27bbd51f34e5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_FinrankIntertw
import Theorems.Thm_PI_Dv_GLP_eS_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Representation
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.GLP
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V)
    (T : GoodSet K G) (s : T.S) :
    ρ.asAlgebraHom (eS T s) = ∑ x : G, cS T s x • ρ x := by
  rw [eS_eq, map_sum]
  simp [map_smul, Representation.asAlgebraHom_of]
end PI.Dv.GLP

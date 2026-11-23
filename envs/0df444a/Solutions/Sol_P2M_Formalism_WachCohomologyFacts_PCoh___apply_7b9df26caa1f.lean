-- Prove2me | solution 1 for P2M_Formalism_WachCohomologyFacts_PCoh___apply_7b9df26caa1f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:37.000805+00:00
-- url     : https://prove2.me/submissions/736dd5dc-7799-4846-9df8-89309dda7a5d

import Definitions.Def_Formalism_FrobeniusContraction_Statement
import Definitions.Def_Formalism_FrobeniusContraction_FrobeniusContractionProofs_FiniteCocyclesLeCocycles

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WachCohomologyFacts Formalism.WachCohomologyFacts.PCoh
open Formalism.WachCohomologyFacts
variable {O A AA : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
  [Algebra A AA] [IsScalarTower O A AA] {B : Base O A} {E : Amb B AA} {n : ℕ}
  {V : Type} [AddCommGroup V] [Module AA V] [Module A V] [IsScalarTower A AA V] [Module O V]
  [IsScalarTower O AA V] (W : WachDatum E n V)
namespace Formalism.WachCohomologyFacts.PCoh
theorem _root_.solution (x : ZMod n → V) (j : ZMod n) : W.Φ x j = W.φ (j - 1) (x (j - 1)) := rfl
end Formalism.WachCohomologyFacts.PCoh

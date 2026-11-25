-- Prove2me | solution 1 for P2M_Formalism_WachCohomologyFacts_PCoh____comm_26f0b5ea9b7b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:47:36.165397+00:00
-- url     : https://prove2.me/submissions/79688a9e-2bd4-4013-813d-55f17777ada2

import Definitions.Def_Formalism_FrobeniusContraction_Statement
import Definitions.Def_Formalism_FrobeniusContraction_FrobeniusContractionProofs_FiniteCocyclesLeCocycles
import Theorems.Thm_P2M_Formalism_WachCohomologyFacts_PCoh___apply_7b9df26caa1f
import Theorems.Thm_P2M_Formalism_WachCohomologyFacts_PCoh___apply_5d4b3ae17b59

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
theorem _root_.solution (x : ZMod n → V) : W.Γ (W.Φ x) = W.Φ (W.Γ x) := by
  funext j
  rw [Γ_apply, Φ_apply, Φ_apply, Γ_apply, W.comm (j - 1) (x (j - 1)), sub_add_cancel]
end Formalism.WachCohomologyFacts.PCoh

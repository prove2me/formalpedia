-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.perturbTop_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:10:05.975481+00:00
-- url     : https://prove2.me/submissions/3f964c23-ffe9-4302-b9c9-c28c40d09a0f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Preimages
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26RXCoarseInfluence BDL26RXInfluenceBounds MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (d : Nat) (i : StepIndex d)
variable (n : Nat)
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
theorem _root_.solution (sigma : TopInput S n)
    (e : (indexedFamily S (n+2)).Cochain1 (TopIndex (n+2))) :
    sigma.val + (perturbTop S n sigma e).val =
      (indexedFamily S (n+2)).coboundary1 (TopIndex (n+2)) e := by
  funext z
  change sigma.val z + (sigma.val z + _) = _
  rw [← add_assoc, ZModModule.add_self, zero_add]
end QEC.Coding.BDL26HistorySyndromeSensitivity

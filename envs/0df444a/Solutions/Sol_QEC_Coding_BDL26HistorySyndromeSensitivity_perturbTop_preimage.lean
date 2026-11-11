-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.perturbTop_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:10:01.887177+00:00
-- url     : https://prove2.me/submissions/177d4b70-2a7f-4c65-9cb5-9f4bf6006d82

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
    ∃ a : (indexedFamily S (n+2)).Cochain1 (TopIndex (n+2)),
      (indexedFamily S (n+2)).coboundary1 (TopIndex (n+2)) a = sigma.val ∧
      (indexedFamily S (n+2)).coboundary1 (TopIndex (n+2)) (a+e) =
        (perturbTop S n sigma e).val := by
  obtain ⟨a,ha⟩ := sigma.property
  exact ⟨a,ha,by change _ = sigma.val + _; rw [map_add,ha]⟩
end QEC.Coding.BDL26HistorySyndromeSensitivity

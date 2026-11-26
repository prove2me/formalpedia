-- Prove2me | solution 1 for TunnellMap.sourceRoster_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:30:34.458958+00:00
-- url     : https://prove2.me/submissions/b48e36f4-e6e5-419a-ab92-a1f7bf9e3fdd

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_ComputableRoster

set_option autoImplicit true
open TunnellMap
variable {n : ℤ} [Fintype (BOddRep n)]
open RecordDA
namespace TunnellMap
theorem _root_.solution :
    (sourceRoster n).Pairwise fun a b => bResidualLexKey a ≤ bResidualLexKey b := by
  classical
  letI : LinearOrder (bResidualInvolution n).Orbit :=
    LinearOrder.lift' residualSourceOrbitKey residualSourceOrbitKey_injective
  have hsorted : (residualSourceOrder (n := n)).Pairwise (· ≤ ·) := by
    unfold residualSourceOrder
    exact Finset.pairwise_sort _ _
  rw [sourceRoster]
  refine List.Pairwise.map _ ?_ hsorted
  intro q₁ q₂ h
  exact h
end TunnellMap

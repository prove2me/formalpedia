-- Prove2me | solution 1 for UpperTheory.Mu.host_torsionOrder_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:31:50.534674+00:00
-- url     : https://prove2.me/submissions/e492b51e-9048-42f2-be0d-932b78319db2

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_Monomial
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_HostTorsionOrderLe
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_finrank_cmField
import Theorems.Thm_Formalism_FrobeniusOrbits_finrank_cmField
import Theorems.Thm_Formalism_HC_HostAx_finrank_cmField
import Theorems.Thm_Formalism_L2_SG_NGCut_TorsionTotientBound_torsionOrder_le
import Theorems.Thm_UpperTheory_Mu_torsionOrder_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.BasicNotions
open UpperTheory UpperTheory.Mu
namespace UpperTheory.Mu
theorem _root_.solution {R : Ranks} (H : Host R) : Units.torsionOrder H.E ≤ 8 * R.f ^ 2 := by
  have h := torsionOrder_le H.E
  rw [H.finrank_cmField] at h
  have hn : R.f = 2 * R.ord := rfl
  rw [hn]
  calc Units.torsionOrder H.E ≤ 2 * (4 * R.ord) ^ 2 := h
    _ = 8 * (2 * R.ord) ^ 2 := by ring
end UpperTheory.Mu

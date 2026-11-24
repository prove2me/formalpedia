-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagCoeffBlockPermute_proof_ffd217eb1969
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:10:23.824497+00:00
-- url     : https://prove2.me/submissions/7cd088d2-4064-45f8-bf85-24efe0295c1a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagCoeffBlockPermute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FlagCoeffBlockPermute
theorem _root_.solution : FlagCoeffBlockPermute.Statement := by
  intro f N w P α
  classical
  set E := blockPermuteEquiv f N w with hE
  set β : Fin f × Fin N →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm fun p : Fin f × Fin N => α (p.1, w p.1 p.2) with hβ
  have hmap : Finsupp.mapDomain E β = α := by
    ext q
    obtain ⟨p, rfl⟩ := E.surjective q
    rw [Finsupp.mapDomain_apply E.injective]
    simp [hβ, hE, blockPermuteEquiv]
  have hren : blockPermute f N w P = rename E P := rfl
  rw [hren, ← hmap, coeff_rename_mapDomain E E.injective]
end FlagCoeffBlockPermute
end GroundTheory.Heights₂.Heights.RestTerms

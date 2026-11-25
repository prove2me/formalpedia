-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_proof_666dbd5f83b0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:45:17.415322+00:00
-- url     : https://prove2.me/submissions/8b7d2c28-52e5-45cc-8027-b3483f6697d0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechH0SectionsHypothesesLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsMemSupport
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_toKer_bijective_f431c159934d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.CechZerothCohomologySections
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.CechZerothCohomologySections
theorem _root_.solution : CechZerothCohomologySections.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F hx
  have hp : (Cech.bdry (fun I => F.sub I) F.res 0).comap
      (LinearMap.ker (Cech.d (fun I => F.sub I) F.res 0)).subtype = ⊥ := by
    rw [show Cech.bdry (fun I => F.sub I) F.res 0 = ⊥ from rfl, Submodule.comap_bot,
      Submodule.ker_subtype]
  exact ⟨(Submodule.quotEquivOfEqBot _ hp).trans
    (LinearEquiv.ofBijective (toKer F) (toKer_bijective F hx)).symm⟩
end GroundTheory.Heights₂.Heights.Kleiman.CechZerothCohomologySections

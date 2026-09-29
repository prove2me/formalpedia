-- Prove2me | solution 1 for Rep.nonempty_twist_inv_twist_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/0295a156-debc-5867-823b-fbae5c4e3269

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_nonempty_twist_inv_twist_iso

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation"
open scoped Classical

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation"
open scoped Classical

theorem solution {k : Type} [CommRing k] {G : Type} [Group G] (N : Rep.{0} k G) (χ : G →* kˣ) :
    Nonempty ((N.twist χ⁻¹).twist χ ≅ N) := by
  refine ⟨Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl k N) fun g => ?_)⟩
  apply LinearMap.ext
  intro v
  show (N.ρ.twist χ⁻¹).twist χ g v = N.ρ g v
  rw [Representation.twist_apply_apply, Representation.twist_apply_apply, smul_smul, MonoidHom.inv_apply,
    Units.mul_inv, one_smul]

end S_Rep_nonempty_twist_inv_twist_iso
end P2MW
export P2MW.S_Rep_nonempty_twist_inv_twist_iso (solution)

-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_nestedHomeomorph___apply_068446922cac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:43:27.656994+00:00
-- url     : https://prove2.me/submissions/1f62422b-dbf4-443e-bd7d-c8c357d6a7c3

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_BridgeNested
import Theorems.Thm_GroundTheory_ProfCoh_nestedHomeomorph_succ_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory TopRep ContRepresentation
universe u v w
variable {k G : Type u} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]
variable (X : TopRep.{u} k G)
namespace GroundTheory.ProfCoh
theorem _root_.solution (m : ℕ) (g : G) (a : resolutionX X m) (x : Fin m → G) :
    nestedHomeomorph X m ((resolutionX X m).ρ g a) x =
      X.ρ g (nestedHomeomorph X m a fun i => g⁻¹ * x i) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [nestedHomeomorph_succ_apply, nestedHomeomorph_succ_apply]
    exact ih _ _
end GroundTheory.ProfCoh

-- Prove2me | solution 1 for Rep.nonempty_twist_iso_trivial_twist_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/ffa84084-b754-5d52-963b-021801189605

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

namespace P2MW.S_Rep_nonempty_twist_iso_trivial_twist_tensor

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation"
open scoped Classical

open scoped TensorProduct

theorem solution
    {k : Type} [CommRing k] {G : Type} [Group G] (N : Rep.{0} k G) (χ : G →* kˣ) :
    Nonempty (N.twist χ ≅ (Rep.trivial k G k).twist χ ⊗ N) := by
  refine ⟨Rep.mkIso (Representation.Equiv.mk (TensorProduct.lid k N).symm fun g => ?_)⟩
  apply LinearMap.ext
  intro v
  show (TensorProduct.lid k N).symm ((N.ρ.twist χ) g v) =
    (Rep.ρ ((Rep.trivial k G k).twist χ ⊗ N)) g ((TensorProduct.lid k N).symm v)
  rw [Representation.twist_apply_apply, TensorProduct.lid_symm_apply, TensorProduct.lid_symm_apply,
    Rep.tensor_ρ, Representation.tprod_apply, TensorProduct.map_tmul]
  show (1 : k) ⊗ₜ[k] ((χ g : k) • N.ρ g v) = ((Rep.trivial k G k).ρ.twist χ) g 1 ⊗ₜ[k] N.ρ g v
  rw [Representation.twist_apply_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  congr 1

end S_Rep_nonempty_twist_iso_trivial_twist_tensor
end P2MW
export P2MW.S_Rep_nonempty_twist_iso_trivial_twist_tensor (solution)

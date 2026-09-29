-- Prove2me | solution 1 for Submodule.finrank_comap_eq_finrank_ker_add_finrank_range_inf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/46175c62-0884-53e5-8b1f-467f1dafba4b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_finrank_comap_eq_finrank_ker_add_finrank_range_inf

open Module

theorem solution
    {k : Type*} [Field k] {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (f : V →ₗ[k] W) (N : Submodule k W) [FiniteDimensional k (N.comap f)] :
    finrank k (N.comap f)
      = finrank k (LinearMap.ker f) + finrank k (LinearMap.range f ⊓ N : Submodule k W) := by
  have hker : LinearMap.ker f ≤ N.comap f := fun x hx => by
    simp only [Submodule.mem_comap, LinearMap.mem_ker.mp hx, Submodule.zero_mem]
  have h := LinearMap.finrank_range_add_finrank_ker (f ∘ₗ (N.comap f).subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_comap_eq,
    LinearMap.ker_comp, (Submodule.comapSubtypeEquivOfLe hker).finrank_eq] at h
  omega

end S_Submodule_finrank_comap_eq_finrank_ker_add_finrank_range_inf
end P2MW
export P2MW.S_Submodule_finrank_comap_eq_finrank_ker_add_finrank_range_inf (solution)

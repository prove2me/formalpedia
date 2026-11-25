-- Prove2me | solution 1 for P2M_Formalism_L2_G_Cmp_Fib_K__split_0aa688ac5c40
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:45:21.922317+00:00
-- url     : https://prove2.me/submissions/26ba81e3-8a06-49ea-8497-0bc91133944f

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsFib

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Cmp
open Formalism.UG
open Formalism.L2.G.Cmp.Fib
variable {G Gp : Type} [Group G] [Group Gp] {K K' : Subgroup G} {Kp : Subgroup Gp} (X : Fib K K' Kp) (H : Subgroup G)
namespace Formalism.L2.G.Cmp.Fib
theorem _root_.solution (x : G) (hx : x ∈ K') : (X.j (X.pr x))⁻¹ * x ∈ K := by
  rw [X.K_iff]
  refine ⟨K'.mul_mem (K'.inv_mem (X.j_mem _)) hx, ?_⟩
  rw [map_mul, map_inv, X.pr_j, inv_mul_cancel]
  exact Kp.one_mem
end Formalism.L2.G.Cmp.Fib

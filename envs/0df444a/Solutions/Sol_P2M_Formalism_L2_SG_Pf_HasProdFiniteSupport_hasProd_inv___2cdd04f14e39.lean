-- Prove2me | solution 1 for P2M_Formalism_L2_SG_Pf_HasProdFiniteSupport_hasProd_inv___2cdd04f14e39
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:08:53.52605+00:00
-- url     : https://prove2.me/submissions/2072cc87-e76b-46ba-803c-7385292b2b9c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_HasProdFiniteSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.HasProdFiniteSupport
open Filter Topology
variable {ι : Type*}
namespace Formalism.L2.SG.Pf.HasProdFiniteSupport
theorem _root_.solution {f : ι → ℝ} {a : ℝ} (h : HasProd f a) (ha : a ≠ 0) :
    HasProd (fun i => (f i)⁻¹) a⁻¹ := by
  unfold HasProd at h ⊢
  refine (h.inv₀ ha).congr (fun s => ?_)
  exact (Finset.prod_inv_distrib f).symm
end Formalism.L2.SG.Pf.HasProdFiniteSupport

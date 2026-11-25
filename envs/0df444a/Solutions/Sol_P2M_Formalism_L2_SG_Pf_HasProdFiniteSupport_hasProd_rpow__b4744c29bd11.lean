-- Prove2me | solution 1 for P2M_Formalism_L2_SG_Pf_HasProdFiniteSupport_hasProd_rpow__b4744c29bd11
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:02:24.23361+00:00
-- url     : https://prove2.me/submissions/01b0bff2-d888-49b1-ac4d-32c11c482834

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
theorem _root_.solution {f : ι → ℝ} {a : ℝ} (p : ℝ) (hf : ∀ i, 0 ≤ f i) (h : HasProd f a) (ha : a ≠ 0) :
    HasProd (fun i => f i ^ p) (a ^ p) := by
  unfold HasProd at h ⊢
  refine (h.rpow_const (Or.inl ha)).congr (fun s => ?_)
  exact (Real.finsetProd_rpow s f (fun i _ => hf i) p).symm
end Formalism.L2.SG.Pf.HasProdFiniteSupport

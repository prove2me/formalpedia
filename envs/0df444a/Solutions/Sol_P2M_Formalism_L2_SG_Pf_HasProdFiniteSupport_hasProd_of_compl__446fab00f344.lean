-- Prove2me | solution 1 for P2M_Formalism_L2_SG_Pf_HasProdFiniteSupport_hasProd_of_compl__446fab00f344
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:02:21.367935+00:00
-- url     : https://prove2.me/submissions/71b87019-4ee2-4a41-9365-66c6917d3e78

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
theorem _root_.solution (s : Finset ι) {f : ι → ℝ} {a : ℝ}
    (h : HasProd (fun i : {i // i ∉ s} => f i) a) : HasProd f (a * ∏ i : s, f i) := by
  classical
  have h1 : HasProd ((↑s : Set ι)ᶜ.mulIndicator f) a :=
    (hasProd_subtype_iff_mulIndicator (s := (↑s : Set ι)ᶜ)).mp h
  have h2 : HasProd ((↑s : Set ι).mulIndicator f) (∏ i : s, f i) :=
    (hasProd_subtype_iff_mulIndicator (s := (↑s : Set ι))).mp (hasProd_fintype _)
  have h3 := h1.mul h2
  convert h3 using 1
  · funext i
    by_cases hp : i ∈ s <;> simp [Set.mulIndicator, hp]
end Formalism.L2.SG.Pf.HasProdFiniteSupport

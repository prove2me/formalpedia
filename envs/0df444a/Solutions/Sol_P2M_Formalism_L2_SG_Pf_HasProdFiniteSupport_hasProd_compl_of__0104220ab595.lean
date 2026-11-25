-- Prove2me | solution 1 for P2M_Formalism_L2_SG_Pf_HasProdFiniteSupport_hasProd_compl_of__0104220ab595
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:44.692806+00:00
-- url     : https://prove2.me/submissions/e557b07c-18a4-4d04-9008-88a5e7b9a957

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_HasProdFiniteSupport
import Theorems.Thm_P2M_Formalism_L2_SG_Pf_HasProdFiniteSupport_hasProd_inv___2cdd04f14e39

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
theorem _root_.solution (s : Finset ι) {f : ι → ℝ} {a : ℝ} (h : HasProd f a) (hf : ∀ i ∈ s, f i ≠ 0) :
    HasProd (fun i : {i // i ∉ s} => f i) (a * (∏ i : s, f i)⁻¹) := by
  classical
  have h2 : HasProd (fun i => ((↑s : Set ι).mulIndicator f i)⁻¹) (∏ i : s, f i)⁻¹ := by
    have h0 : HasProd ((↑s : Set ι).mulIndicator f) (∏ i : s, f i) :=
      (hasProd_subtype_iff_mulIndicator (s := (↑s : Set ι))).mp (hasProd_fintype _)
    exact hasProd_inv₀' h0 (Finset.prod_ne_zero_iff.mpr fun i _ => hf i i.2)
  have h3 := h.mul h2
  have h4 : HasProd ((↑s : Set ι)ᶜ.mulIndicator f) (a * (∏ i : s, f i)⁻¹) := by
    convert h3 using 1
    funext i
    by_cases hp : i ∈ s
    · simp [Set.mulIndicator, hp, hf i hp]
    · simp [Set.mulIndicator, hp]
  exact (hasProd_subtype_iff_mulIndicator (s := (↑s : Set ι)ᶜ)).mpr h4
end Formalism.L2.SG.Pf.HasProdFiniteSupport

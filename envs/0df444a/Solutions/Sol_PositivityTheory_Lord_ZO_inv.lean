-- Prove2me | solution 1 for PositivityTheory.Lord.ZO.inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:48.468082+00:00
-- url     : https://prove2.me/submissions/3a89acda-0d95-42d2-8322-9e0aee1d4440

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_MeromorphicAtProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open PositivityTheory PositivityTheory.Lord
variable {f g : ℂ → ℂ} {x : ℂ} {k l m n : ℕ}
namespace PositivityTheory.Lord
namespace ZO
theorem _root_.solution (hf : ZO f x m) : PO (fun s => (f s)⁻¹) x m := by
  obtain ⟨u, hu, hux, hev⟩ := hf
  refine ⟨fun s => (u s)⁻¹, hu.fun_inv hux, ?_⟩
  have hne : ∀ᶠ s in 𝓝[≠] x, u s ≠ 0 :=
    nhdsWithin_le_nhds (hu.continuousAt.eventually_ne hux)
  filter_upwards [hev, hne, self_mem_nhdsWithin] with s hs hus hsx
  have hsx' : s - x ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hsx)
  rw [hs, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hsx'), one_mul]
end ZO
end PositivityTheory.Lord

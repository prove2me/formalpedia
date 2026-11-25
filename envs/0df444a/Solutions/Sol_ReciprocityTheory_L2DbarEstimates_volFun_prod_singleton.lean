-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.volFun_prod_singleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:26:02.777357+00:00
-- url     : https://prove2.me/submissions/7fd5e4fb-0954-4ac4-913d-b7f669dee5a9

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IsLocalHomeomorphCompFst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} (n : ℕ) (z : M → V n) (p : ℕ) (B : Set M) (i : Fin p) :
    volFun n (fun q : M × Fin p => z q.1) (B ×ˢ {i}) = volFun n z B := by
  unfold volFun
  refine lintegral_congr fun y => ?_
  have h : (B ×ˢ {i}) ∩ (fun q : M × Fin p => z q.1) ⁻¹' {y} = (fun x => (x, i)) '' (B ∩ z ⁻¹' {y}) := by
    ext ⟨x, j⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_singleton_iff, Set.mem_preimage,
      Set.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hx, rfl⟩, hy⟩
      exact ⟨x, ⟨hx, hy⟩, rfl, rfl⟩
    · rintro ⟨x', ⟨hx, hy⟩, rfl, rfl⟩
      exact ⟨⟨hx, rfl⟩, hy⟩
  rw [h, (Prod.mk_left_injective i).encard_image]
end ReciprocityTheory.L2DbarEstimates

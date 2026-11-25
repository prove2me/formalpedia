-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.unitaryTransvection_zero_second_mem_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:28:20.427096+00:00
-- url     : https://prove2.me/submissions/7338234f-96b8-4d7c-b9e4-937cc7bb41bb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_UnitaryTransvectionZeroSecondMemClosure
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_zero_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable {e f : ι → K} (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include hσ hJ he hff hef
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution {c : K} (hc : σ c = -c) : eich σ J f 0 c ∈ Submonoid.closure (eichSet σ J e f) := by
  refine Submonoid.subset_closure (Or.inr ⟨0, c, hf_zero_left σ J f, hf_zero_left σ J e, ?_, rfl⟩)
  rw [hc, hf_zero_left]
  ring
end ReciprocityTheory.ChartRestriction.G.SA

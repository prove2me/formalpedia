-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.ae_slice_prodFin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:16:58.386799+00:00
-- url     : https://prove2.me/submissions/9306e2c4-e7bd-42c5-8bc5-29d7371f49ee

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_NeedBergmanClosed
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaOps
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_NearContinuousOfSmoothR
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_OntoWithBoundTop
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_VolProdFinApply
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_vol_prodFin_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ)
    {P : M × Fin p → Prop} (h : ∀ᵐ q ∂vol n (fun q : M × Fin p => z q.1), P q) (i : Fin p) :
    ∀ᵐ x ∂vol n z, P (x, i) := by
  rw [ae_iff] at h ⊢
  obtain ⟨T, hsub, hT, hT0⟩ := exists_measurable_superset_of_null h
  have hsub' : {x : M | ¬P (x, i)} ⊆ (fun x : M => (x, i)) ⁻¹' T := fun x hx => hsub hx
  refine measure_mono_null hsub' ?_
  have hsum := vol_prodFin_apply n z hz p T hT
  rw [hT0] at hsum
  exact (Finset.sum_eq_zero_iff.1 hsum.symm) i (Finset.mem_univ i)
end ReciprocityTheory.L2DbarEstimates.H

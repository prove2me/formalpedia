-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.ae_fst_prodFin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:10:36.881942+00:00
-- url     : https://prove2.me/submissions/6809e468-1559-41b4-87dc-285a43fd75fe

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
theorem _root_.solution (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) {P : M → Prop}
    (h : ∀ᵐ x ∂vol n z, P x) : ∀ᵐ q ∂vol n (fun q : M × Fin p => z q.1), P q.1 := by
  rw [ae_iff] at h ⊢
  obtain ⟨T, hsub, hT, hT0⟩ := exists_measurable_superset_of_null h
  have hsub' : {q : M × Fin p | ¬P q.1} ⊆ Prod.fst ⁻¹' T := fun q hq => hsub hq
  refine measure_mono_null hsub' ?_
  rw [vol_prodFin_apply n z hz p _ (hT.preimage measurable_fst)]
  exact Finset.sum_eq_zero fun i _ => hT0
end ReciprocityTheory.L2DbarEstimates.H

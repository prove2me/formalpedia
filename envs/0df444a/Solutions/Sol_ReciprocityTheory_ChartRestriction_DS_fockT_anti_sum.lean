-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.fockT_anti_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:21:56.864751+00:00
-- url     : https://prove2.me/submissions/f91fb52f-634e-4aea-9189-191ea6c70383

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_FockTA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {R : Type*} [Ring R] {ι κ : Type*} (s : Finset ι) (t : Finset κ) (G : R)
    (A B : ι → κ → R) (hA : ∀ i k, G * A i k = A i k * G) (hB : ∀ i k, G * B i k = -(B i k * G)) :
    G * ∑ i ∈ s, ∑ k ∈ t, A i k * B i k = -((∑ i ∈ s, ∑ k ∈ t, A i k * B i k) * G) := by
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  calc G * (A i k * B i k) = A i k * (G * B i k) := by rw [← mul_assoc, hA, mul_assoc]
    _ = -(A i k * B i k * G) := by rw [hB, mul_neg, mul_assoc]
end ReciprocityTheory.ChartRestriction.DS

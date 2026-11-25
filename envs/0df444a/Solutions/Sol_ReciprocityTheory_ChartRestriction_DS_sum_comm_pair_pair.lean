-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.sum_comm_pair_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:26:18.947925+00:00
-- url     : https://prove2.me/submissions/ea47be74-0647-45a7-a875-d5e4ed0f3d37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqA

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
theorem _root_.solution {R : Type*} [AddCommMonoid R] {ι κ ι' κ' : Type*} (s : Finset ι) (s' : Finset ι')
    (t : Finset κ) (t' : Finset κ') (f : ι → ι' → κ → κ' → R) :
    ∑ a ∈ s, ∑ b ∈ s', ∑ i ∈ t, ∑ j ∈ t', f a b i j = ∑ i ∈ t, ∑ j ∈ t', ∑ a ∈ s, ∑ b ∈ s', f a b i j := by
  calc _ = ∑ a ∈ s, ∑ i ∈ t, ∑ b ∈ s', ∑ j ∈ t', f a b i j :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a ∈ s, ∑ i ∈ t, ∑ j ∈ t', ∑ b ∈ s', f a b i j :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i ∈ t, ∑ a ∈ s, ∑ j ∈ t', ∑ b ∈ s', f a b i j := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_comm
end ReciprocityTheory.ChartRestriction.DS

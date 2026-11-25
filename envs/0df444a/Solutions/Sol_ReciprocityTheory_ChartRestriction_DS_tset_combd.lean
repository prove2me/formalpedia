-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.tset_combd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:40:48.279305+00:00
-- url     : https://prove2.me/submissions/bd941747-561f-4e6d-bf67-6fafda21fc9a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_MultOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IsInLieAlgebraISmulAddConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_HidaSetting

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
open scoped Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {H : Type*} [AddCommGroup H] [Module ℂ H] (k : Fin n → Fin n → ℂ)
    (hu : ∀ s b, ∑ d, k s d * star (k b d) = if s = b then 1 else 0) (X : Fin n → Fin n → Fin n → H)
    (r : Fin n) :
    ∑ d, star (k r d) • ∑ s, ∑ a, ∑ b, (k a d * star (k b s)) • X a b s =
      ∑ s, ∑ b, star (k b s) • X r b s := by
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  have ha : ∀ a, ∑ d, ∑ b, (star (k r d) * (k a d * star (k b s))) • X a b s =
      ∑ b, (star (k b s) * if a = r then 1 else 0) • X a b s := by
    intro a
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_smul, ← hu a r, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun d _ => by ring
  simp only [ha, mul_ite, mul_one, mul_zero, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
end ReciprocityTheory.ChartRestriction.DS

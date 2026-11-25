-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.tset_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:28:19.989954+00:00
-- url     : https://prove2.me/submissions/809e7eb4-b22c-47d7-ac76-d92f79effa6a

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
    (s : Fin n) :
    ∑ d, k s d • ∑ r, ∑ a, ∑ b, (k a r * star (k b d)) • X a b r = ∑ r, ∑ a, k a r • X a s r := by
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  have hb : ∀ b, ∑ d, (k s d * (k a r * star (k b d))) • X a b r =
      (k a r * if s = b then 1 else 0) • X a b r := by
    intro b
    rw [← Finset.sum_smul, ← hu s b, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun d _ => by ring
  simp only [hb, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
end ReciprocityTheory.ChartRestriction.DS

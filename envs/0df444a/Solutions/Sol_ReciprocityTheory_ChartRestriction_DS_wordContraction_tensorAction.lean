-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.wordContraction_tensorAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:38:55.077919+00:00
-- url     : https://prove2.me/submissions/90183eca-faa5-4452-9216-8c9a73a6056f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_wordContraction_apply
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_factorAd_apply__c08584207034
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_commutator_rootWordProduct
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sum_ite_update_reindex
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_positionTensorAction_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section PhiAux
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
private theorem linearMap_apply_ite_zero (T : Module.End ℂ M) (c : Prop) [Decidable c] (x : M) :
    T (if c then x else 0) = if c then T x else 0 := by
  split_ifs <;> simp
private theorem ite_linearMap_zero_apply (T : Module.End ℂ M) (c : Prop) [Decidable c] (x : M) :
    (if c then T else 0) x = if c then T x else 0 := by
  split_ifs <;> simp
end PhiAux
section Phi
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
end Phi
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE : IsGlRep E) (k : ℕ) (a b : Fin n) (F : Big n k M) :
    phi E k (bAct E k a b F) = E a b (phi E k F) := by
  have h1 : ∀ i : Fin k, ∑ κ : Fin k → Fin n × Fin n,
      (if (κ i).1 = a then word E κ (F (Function.update κ i (b, (κ i).2))) else 0) =
      ∑ κ : Fin k → Fin n × Fin n,
      (if (κ i).1 = b then word E (Function.update κ i (a, (κ i).2)) (F κ) else 0) := fun i =>
    sum_ite_update_reindex i (fun p => p.1 = a) (fun p => p.1 = b) (fun p => (b, p.2)) (fun p => (a, p.2))
      (fun _ _ => rfl) (fun _ _ => rfl) (fun p hp => Prod.ext hp.symm rfl)
      (fun p hp => Prod.ext hp.symm rfl) (fun κ => word E κ) F
  have h2 : ∀ i : Fin k, ∑ κ : Fin k → Fin n × Fin n,
      (if (κ i).2 = b then word E κ (F (Function.update κ i ((κ i).1, a))) else 0) =
      ∑ κ : Fin k → Fin n × Fin n,
      (if (κ i).2 = a then word E (Function.update κ i ((κ i).1, b)) (F κ) else 0) := fun i =>
    sum_ite_update_reindex i (fun p => p.2 = b) (fun p => p.2 = a) (fun p => (p.1, a)) (fun p => (p.1, b))
      (fun _ _ => rfl) (fun _ _ => rfl) (fun p hp => Prod.ext rfl hp.symm)
      (fun p hp => Prod.ext rfl hp.symm) (fun κ => word E κ) F
  have hc : ∀ κ : Fin k → Fin n × Fin n, E a b (word E κ (F κ)) = word E κ (E a b (F κ)) +
      ∑ i, ((if (κ i).1 = b then word E (Function.update κ i (a, (κ i).2)) (F κ) else 0) -
        (if (κ i).2 = a then word E (Function.update κ i ((κ i).1, b)) (F κ) else 0)) := by
    intro κ
    have h := congrArg (fun T : Module.End ℂ M => T (F κ)) (commutator_rootWordProduct hE a b κ)
    first
    | simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply,
        ite_linearMap_zero_apply] at h
    | simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.coe_sum, Finset.sum_apply,
        ite_linearMap_zero_apply] at h
    first
    | exact sub_eq_iff_eq_add'.mp h
    | (rw [← h]; abel)
  rw [wordContraction_apply, wordContraction_apply, map_sum]
  simp only [positionTensorAction_apply, factorAd_apply', map_add, map_sum, map_sub,
    linearMap_apply_ite_zero, hc, Finset.sum_add_distrib]
  congr 1
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, h1 i, h2 i]
end ReciprocityTheory.ChartRestriction.DS

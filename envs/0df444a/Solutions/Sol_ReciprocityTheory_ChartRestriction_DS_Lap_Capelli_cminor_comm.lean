-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.cminor_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:20:41.750014+00:00
-- url     : https://prove2.me/submissions/c465e48a-6bfc-4faf-8247-3bec30c71cd9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliCentralStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ProdOfFnUpdateEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_prod_ofFn_update_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_comm_prod_ofFn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_capEntry_comm
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
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
section SlopeTestRemainingChoices
variable {𝒰 : Type*} [Ring 𝒰]
end SlopeTestRemainingChoices
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)
private theorem prod_ofFn_update_sub' {p : ℕ} (f : Fin p → 𝒰) (j : Fin p) (u v : 𝒰) :
    (List.ofFn (Function.update f j (u - v))).prod =
      (List.ofFn (Function.update f j u)).prod - (List.ofFn (Function.update f j v)).prod := by
  obtain ⟨A, B, h⟩ := prod_ofFn_update_eq f j
  rw [h, h, h]
  noncomm_ring
private theorem prod_ofFn_update_ite' {p : ℕ} (f : Fin p → 𝒰) (j : Fin p) (P : Prop) [Decidable P]
    (w : 𝒰) :
    (List.ofFn (Function.update f j (if P then w else 0))).prod =
      if P then (List.ofFn (Function.update f j w)).prod else 0 := by
  obtain ⟨A, B, h⟩ := prod_ofFn_update_eq f j
  split_ifs
  · rfl
  · rw [h, mul_zero, zero_mul]
private theorem sum_ite_sum_comm {α β : Type*} [Fintype α] [Fintype β] (P : α → Prop)
    [DecidablePred P] (g : α → β → 𝒰) :
    (∑ t, if P t then ∑ σ, g t σ else 0) = ∑ σ, ∑ t, if P t then g t σ else 0 := by
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp
private theorem sum_comp_perm_eq_sum {p : ℕ} (σ : Equiv.Perm (Fin p)) (g : Fin p → 𝒰) :
    ∑ t, g t = ∑ j, g (σ j) :=
  (Equiv.sum_comp σ g).symm
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution (hE : GlRelR E) (a b : Fin n) {p : ℕ} (R C : Fin p → Fin n) (x : ℂ) :
    E a b * cminor E R C x - cminor E R C x * E a b =
      (∑ t : Fin p, if R t = b then cminor E (Function.update R t a) C x else 0) -
        ∑ t : Fin p, if C t = a then cminor E R (Function.update C t b) x else 0 := by
  unfold cminor
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, mul_smul_comm, smul_mul_assoc,
    ← smul_sub, comm_prod_ofFn, capEntry_comm E hE, prod_ofFn_update_sub', prod_ofFn_update_ite']
  simp only [Finset.smul_sum, smul_sub, Finset.sum_sub_distrib]
  congr 1
  · rw [sum_ite_sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    conv_rhs => rw [sum_comp_perm_eq_sum σ]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : R (σ j) = b
    · rw [if_pos h.symm, if_pos h]
      congr 1
      congr 1
      congr 1
      funext k
      by_cases hk : k = j
      · subst hk
        simp
      · simp [Function.update_apply, hk, σ.injective.ne hk]
    · rw [if_neg (Ne.symm h), if_neg h, smul_zero]
  · rw [sum_ite_sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : C j = a
    · rw [if_pos h, if_pos h]
      congr 1
      congr 1
      congr 1
      funext k
      by_cases hk : k = j
      · subst hk
        simp
      · simp [Function.update_apply, hk]
    · rw [if_neg h, if_neg h, smul_zero]
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

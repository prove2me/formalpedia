-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.casimir_pm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:24:41.493815+00:00
-- url     : https://prove2.me/submissions/6eb11955-a73d-477b-9ae7-004416b83d5d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_csq_sum_univ_pm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimirK_pm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_two_rho_sum

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
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (ε : Fin n → Bool) :
    casimir E = casimirK ε E + (2 : ℂ) • ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, E i a * E a i -
      (2 : ℂ) • ∑ a, ((rhoHol ε a : ℝ) : ℂ) • E a a := by
  have hsplit : casimir E = (∑ a ∈ plusIdx ε, ∑ b ∈ plusIdx ε, E a b * E b a +
      ∑ a ∈ plusIdx ε, ∑ b ∈ minusIdx ε, E a b * E b a) +
      (∑ a ∈ minusIdx ε, ∑ b ∈ plusIdx ε, E a b * E b a +
      ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε, E a b * E b a) := by
    unfold casimir
    rw [csq_sum_univ_pm ε]
    congr 1
    · rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => csq_sum_univ_pm ε _
    · rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => csq_sum_univ_pm ε _

  have h1 : ∀ i a : Fin n, E a i * E i a = E i a * E a i - E i i + E a a := by
    intro i a
    have h := hE i a a i
    rw [if_pos rfl, if_pos rfl] at h
    rw [sub_add, ← h]
    abel
  have hcross : ∑ a ∈ minusIdx ε, ∑ b ∈ plusIdx ε, E a b * E b a =
      ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, E i a * E a i -
        (qOf ε : ℂ) • ∑ i ∈ plusIdx ε, E i i + (pOf ε : ℂ) • ∑ a ∈ minusIdx ε, E a a := by
    rw [Finset.sum_comm]
    calc ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, E a i * E i a
        = ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, (E i a * E a i - E i i + E a a) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => h1 i a
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
          Finset.smul_sum, Nat.cast_smul_eq_nsmul]
        rfl
  have h2 := two_rho_sum ε (fun a => E a a)
  rw [hsplit, casimirK_pm, hcross, h2, two_smul, ← Finset.smul_sum, ← Finset.smul_sum]
  abel
end ReciprocityTheory.ChartRestriction.DS

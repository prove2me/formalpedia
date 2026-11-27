-- Prove2me | solution 1 for PositivityTheory.ThKF0.FinLine.test
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:23:24.412279+00:00
-- url     : https://prove2.me/submissions/c45b4dba-50ea-47d6-9dba-04069058bbfc

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_LagrangianUniqueness_Imports
import Theorems.Thm_PositivityTheory_ThKF0_FinLine_ind_mem
import Theorems.Thm_PositivityTheory_ThKF0_FinLine_uniform
import Theorems.Thm_PositivityTheory_ThKF0_FinLine_decomp
import Theorems.Thm_PositivityTheory_ThKF0_FinLine_off

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Filter Topology
open scoped Classical
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.FinLine
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G]
variable {U₀ : OpenAddSubgroup G} (h₀ : IsCompact (U₀ : Set G)) {P : Set G} {l : (G → ℂ) →ₗ[ℂ] ℂ}
include h₀
namespace PositivityTheory.ThKF0.FinLine
theorem _root_.solution (hP0 : (0 : G) ∈ P) (h1 : ∀ p ∈ P, ∀ φ ∈ SB G, l (fun x => φ (x + p)) = l φ)
    (h2 : ∀ a ∉ P, ∃ χ : G → ℂ, IsLocallyConstant χ ∧ χ a ≠ 1 ∧ ∀ φ ∈ SB G, l (fun x => χ x * φ x) = l φ)
    (h0 : l (ind U₀ 0) = 0) {φ : G → ℂ} (hφ : φ ∈ SB G) : l φ = 0 := by
  have key : ∀ U ≤ U₀, ∀ a, l (ind U a) = if ∃ p ∈ P, p - a ∈ U then l (ind U 0) else 0 := by
    intro U hU a
    split_ifs with h
    · obtain ⟨p, hp, hpa⟩ := h
      rw [← h1 p hp _ (ind_mem h₀ hU a)]
      congr 1
      funext x
      simp only [ind, sub_zero, add_sub_assoc]
      exact if_congr (U.toAddSubgroup.add_mem_cancel_right hpa) rfl rfl
    · refine off h₀ h2 (ind_mem h₀ hU a) fun b hb hbP => h ⟨b, hbP, ?_⟩
      by_contra hc
      exact hb (if_neg hc)
  have zero : ∀ U ≤ U₀, l (ind U 0) = 0 := by
    intro U hU
    obtain ⟨t, ht, e⟩ := decomp (ind_mem h₀ le_rfl 0) U fun u hu x => by
      simp only [ind, sub_zero]
      exact if_congr (U₀.toAddSubgroup.add_mem_cancel_right (hU hu)) rfl rfl
    have h3 : ∀ q ∈ t, ind U₀ 0 q.out = 1 := fun q hq => by
      have := (ht q).1 hq
      unfold ind at this ⊢
      split_ifs at this ⊢ with h
      · rfl
      · exact absurd rfl this
    rw [e, map_sum, Finset.sum_congr rfl fun q hq => by rw [h3 q hq, one_smul, key U hU], ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul] at h0
    refine (mul_eq_zero.1 h0).resolve_left (Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨0, ?_⟩))
    have h4 : (0 : G ⧸ U.toAddSubgroup).out ∈ U :=
      (QuotientAddGroup.eq_zero_iff _).1 (QuotientAddGroup.out_eq' (0 : G ⧸ U.toAddSubgroup))
    refine Finset.mem_filter.2 ⟨(ht _).2 ?_, 0, hP0, by simpa using U.neg_mem h4⟩
    simp [ind, hU h4]
  obtain ⟨U₁, hU₁⟩ := uniform hφ
  obtain ⟨t, -, e⟩ := decomp hφ (U₀ ⊓ U₁) fun u hu => hU₁ u hu.2
  rw [e, map_sum]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [map_smul, key _ inf_le_left, zero _ inf_le_left, ite_self, smul_zero]
end PositivityTheory.ThKF0.FinLine

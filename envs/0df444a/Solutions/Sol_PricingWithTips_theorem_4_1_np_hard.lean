-- Prove2me | solution 1 for PricingWithTips.theorem_4_1_np_hard
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-21T19:51:35.884502+00:00
-- url     : https://prove2.me/submissions/99902c38-5561-4b99-9b97-2e6ab5a7c7b2

import Mathlib
import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_PricingWithTips_NPHardness
import Theorems.Thm_PricingWithTips_threeDM_np_hard

open scoped BigOperators

namespace PricingWithTips

private def loss (n : ℕ) (edge : Fin n → Fin n → Fin n → Bool)
    (A : Allocation (Fin n) (Fin n) (Fin n)) (b : Fin n) : ℝ :=
  match A.assigned b with
  | none => 1
  | some (s, d) => if edge b s d then 0 else 1

private theorem loss_nonneg (n : ℕ) (edge : Fin n → Fin n → Fin n → Bool)
    (A : Allocation (Fin n) (Fin n) (Fin n)) (b : Fin n) :
    0 ≤ loss n edge A b := by
  unfold loss
  cases A.assigned b with
  | none => norm_num
  | some sd =>
    rcases sd with ⟨s, d⟩
    simp only
    split_ifs <;> norm_num

private theorem welfare_eq_card_sub_loss (n : ℕ)
    (edge : Fin n → Fin n → Fin n → Bool)
    (A : Allocation (Fin n) (Fin n) (Fin n)) :
    welfare (marketOf3DM n edge) A =
      (n : ℝ) - ∑ b, loss n edge A b := by
  have hone : (∑ _b : Fin n, (1 : ℝ)) = (n : ℝ) := by simp
  rw [← hone, ← Finset.sum_sub_distrib]
  unfold welfare
  apply Finset.sum_congr rfl
  intro b _
  unfold loss marketOf3DM
  cases h : A.assigned b with
  | none => simp
  | some sd =>
    rcases sd with ⟨s, d⟩
    simp

private theorem welfare_le_card (n : ℕ)
    (edge : Fin n → Fin n → Fin n → Bool)
    (A : Allocation (Fin n) (Fin n) (Fin n)) :
    welfare (marketOf3DM n edge) A ≤ (n : ℝ) := by
  rw [welfare_eq_card_sub_loss]
  have h : 0 ≤ ∑ b, loss n edge A b :=
    Finset.sum_nonneg (fun b _ => loss_nonneg n edge A b)
  linarith

theorem welfare_at_least_iff_equal_card (n : ℕ)
    (edge : Fin n → Fin n → Fin n → Bool) :
    HasWelfareAtLeastCard n edge ↔ HasWelfareEqualCard n edge := by
  constructor
  · rintro ⟨A, h⟩
    exact ⟨A, le_antisymm (welfare_le_card n edge A) h⟩
  · rintro ⟨A, h⟩
    exact ⟨A, h.ge⟩

theorem equilibrium_welfare_at_least_iff_equal_card (n : ℕ)
    (edge : Fin n → Fin n → Fin n → Bool) :
    HasEquilibriumWelfareAtLeastCard n edge ↔
      HasEquilibriumWelfareEqualCard n edge := by
  constructor
  · rintro ⟨A, hEq, h⟩
    exact ⟨A, hEq, le_antisymm (welfare_le_card n edge A) h⟩
  · rintro ⟨A, hEq, h⟩
    exact ⟨A, hEq, h.ge⟩

theorem perfect3DM_iff_welfare_at_least_card (n : ℕ)
    (edge : Fin n → Fin n → Fin n → Bool) :
    HasPerfect3DMatching n edge ↔ HasWelfareAtLeastCard n edge := by
  constructor
  · rintro ⟨A, hall, hedge⟩
    refine ⟨A, ?_⟩
    rw [welfare_eq_card_sub_loss]
    have hzero : (∑ b, loss n edge A b) = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      obtain ⟨s, d, ht⟩ := hall b
      change A.assigned b = some (s, d) at ht
      simp [loss, ht, hedge b s d ht]
    rw [hzero]
    simp
  · rintro ⟨A, hw⟩
    have heq := welfare_eq_card_sub_loss n edge A
    have hsum_nonneg : 0 ≤ ∑ b, loss n edge A b :=
      Finset.sum_nonneg (fun b _ => loss_nonneg n edge A b)
    have hsum : (∑ b, loss n edge A b) = 0 := by linarith
    refine ⟨A, ?_, ?_⟩
    · intro b
      have hle : loss n edge A b ≤ ∑ b', loss n edge A b' :=
        Finset.single_le_sum (fun b' _ => loss_nonneg n edge A b')
          (Finset.mem_univ b)
      have hz : loss n edge A b = 0 := by
        have := loss_nonneg n edge A b
        linarith
      cases h : A.assigned b with
      | none => simp [loss, h] at hz
      | some sd =>
        rcases sd with ⟨s, d⟩
        exact ⟨s, d, h⟩
    · intro b s d ht
      have hle : loss n edge A b ≤ ∑ b', loss n edge A b' :=
        Finset.single_le_sum (fun b' _ => loss_nonneg n edge A b')
          (Finset.mem_univ b)
      have hz : loss n edge A b = 0 := by
        have := loss_nonneg n edge A b
        linarith
      simp only [Allocation.Trades] at ht
      simp [loss, ht] at hz
      by_cases he : edge b s d = true
      · exact he
      · simp [he] at hz

private theorem minimumTip_nonneg_reduction {B S D : Type*}
    [Fintype B] [Fintype S] [Fintype D]
    [DecidableEq B] [DecidableEq S] [DecidableEq D]
    (M : Market B S D) (w t : B → S → ℝ) (b : B) (s : S) :
    0 ≤ minimumTip M w t b s := by
  unfold minimumTip
  apply Real.sInf_nonneg
  intro x hx
  exact hx.1

private theorem minimumTip_zero_reduction {B S D : Type*}
    [Fintype B] [Fintype S] [Fintype D]
    [DecidableEq B] [DecidableEq S] [DecidableEq D]
    (M : Market B S D) (w t : B → S → ℝ) (b : B) (s : S) (d : D)
    (h : CourierAccepts M w t b s 0 d) :
    minimumTip M w t b s = 0 := by
  apply le_antisymm
  · apply csInf_le
    · exact ⟨0, by intro x hx; exact hx.1⟩
    · exact ⟨le_rfl, d, h⟩
  · exact minimumTip_nonneg_reduction M w t b s

private theorem perfect_matching_has_equilibrium (n : ℕ)
    (edge : Fin n → Fin n → Fin n → Bool)
    (A : Allocation (Fin n) (Fin n) (Fin n))
    (hall : ∀ b, ∃ s d, A.Trades b s d)
    (hedge : ∀ b s d, A.Trades b s d → edge b s d = true) :
    HasWithTipEquilibriumAt (marketOf3DM n edge) A := by
  let M := marketOf3DM n edge
  refine ⟨fun _ => 0, fun _ _ => 0, fun _ _ => 0, ?_⟩
  refine ⟨(by intro s; norm_num), (by intro b s; norm_num),
    (by intro b s; norm_num), ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    obtain ⟨s, d, ht⟩ := hall b
    have hA : A.assigned b = some (s, d) := ht
    simp only [hA]
    have hcost : M.cost d b s = 0 := by
      simp [M, marketOf3DM, hedge b s d ht]
    have haccept : CourierAccepts M (fun _ _ => 0) (fun _ _ => 0) b s 0 d := by
      constructor
      · simp [hcost]
      · intro b' s'
        have hc := M.cost_nonneg d b' s'
        simp only [counterfactualTip, ite_self, zero_add, zero_sub]
        rw [hcost]
        linarith
    have htip : minimumTip M (fun _ _ => 0) (fun _ _ => 0) b s = 0 :=
      minimumTip_zero_reduction M (fun _ _ => 0) (fun _ _ => 0) b s d haccept
    refine ⟨htip.symm, ?_, ?_⟩
    · change 0 ≤ 1 - 0 - minimumTip M (fun _ _ => 0) (fun _ _ => 0) b s
      rw [htip]
      norm_num
    · intro s'
      have hnonneg := minimumTip_nonneg_reduction M
        (fun _ _ => 0) (fun _ _ => 0) b s'
      change 1 - 0 - minimumTip M (fun _ _ => 0) (fun _ _ => 0) b s' ≤
        1 - 0 - minimumTip M (fun _ _ => 0) (fun _ _ => 0) b s
      rw [htip]
      linarith
  · intro d b s ht
    have hcost : M.cost d b s = 0 := by
      simp [M, marketOf3DM, hedge b s d ht]
    constructor
    · simp only [courierUtility, zero_add, zero_sub]
      rw [hcost]
      norm_num
    · intro b' s'
      simp only [courierUtility, zero_add, zero_sub]
      rw [hcost]
      linarith [M.cost_nonneg d b' s']
  · intro d _ b s
    simp only [courierUtility, zero_add, zero_sub]
    linarith [M.cost_nonneg d b s]
  · intro s _
    rfl
  · intro b s _
    exact ⟨rfl, rfl⟩

theorem perfect3DM_iff_equilibrium_welfare_at_least_card (n : ℕ)
    (edge : Fin n → Fin n → Fin n → Bool) :
    HasPerfect3DMatching n edge ↔ HasEquilibriumWelfareAtLeastCard n edge := by
  constructor
  · intro h
    rcases h with ⟨A, hall, hedge⟩
    refine ⟨A, perfect_matching_has_equilibrium n edge A hall hedge, ?_⟩
    rw [welfare_eq_card_sub_loss]
    have hzero : (∑ b, loss n edge A b) = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      obtain ⟨s, d, ht⟩ := hall b
      change A.assigned b = some (s, d) at ht
      simp [loss, ht, hedge b s d ht]
    rw [hzero]
    simp
  · rintro ⟨A, _, hw⟩
    exact (perfect3DM_iff_welfare_at_least_card n edge).mpr ⟨A, hw⟩

theorem threeDM_poly_reduces_to_welfare :
    PolyManyOneReduces ThreeDMYes WelfareYes := by
  refine ⟨id, ⟨Turing.idComputableInPolyTime encodeThreeDMInstance⟩, ?_⟩
  rintro ⟨n, edge⟩
  exact (perfect3DM_iff_welfare_at_least_card n edge).trans
    (welfare_at_least_iff_equal_card n edge)

theorem threeDM_poly_reduces_to_equilibrium_welfare :
    PolyManyOneReduces ThreeDMYes EquilibriumWelfareYes := by
  refine ⟨id, ⟨Turing.idComputableInPolyTime encodeThreeDMInstance⟩, ?_⟩
  rintro ⟨n, edge⟩
  exact (perfect3DM_iff_equilibrium_welfare_at_least_card n edge).trans
    (equilibrium_welfare_at_least_iff_equal_card n edge)

theorem welfare_language_eq_threeDM : WelfareYes = ThreeDMYes := by
  funext I
  apply propext
  rcases I with ⟨n, edge⟩
  exact ((perfect3DM_iff_welfare_at_least_card n edge).trans
    (welfare_at_least_iff_equal_card n edge)).symm

theorem equilibrium_welfare_language_eq_threeDM :
    EquilibriumWelfareYes = ThreeDMYes := by
  funext I
  apply propext
  rcases I with ⟨n, edge⟩
  exact ((perfect3DM_iff_equilibrium_welfare_at_least_card n edge).trans
    (equilibrium_welfare_at_least_iff_equal_card n edge)).symm

theorem welfare_hard_for_of_threeDM_hard_for
    (sourceClass : Set (ThreeDMInstance → Prop))
    (h : HardFor sourceClass ThreeDMYes) :
    HardFor sourceClass WelfareYes := by
  rwa [welfare_language_eq_threeDM]

theorem equilibrium_welfare_hard_for_of_threeDM_hard_for
    (sourceClass : Set (ThreeDMInstance → Prop))
    (h : HardFor sourceClass ThreeDMYes) :
    HardFor sourceClass EquilibriumWelfareYes := by
  rwa [equilibrium_welfare_language_eq_threeDM]

theorem welfare_np_hard_of_threeDM_np_hard
    (h : NPHardMarketPredicate ThreeDMYes) :
    NPHardMarketPredicate WelfareYes := by
  intro Γ L hL
  obtain ⟨f, hf, hcorrect⟩ := h Γ L hL
  refine ⟨f, hf, ?_⟩
  intro x
  exact (hcorrect x).trans (by
    rw [welfare_language_eq_threeDM])

theorem equilibrium_welfare_np_hard_of_threeDM_np_hard
    (h : NPHardMarketPredicate ThreeDMYes) :
    NPHardMarketPredicate EquilibriumWelfareYes := by
  intro Γ L hL
  obtain ⟨f, hf, hcorrect⟩ := h Γ L hL
  refine ⟨f, hf, ?_⟩
  intro x
  exact (hcorrect x).trans (by
    rw [equilibrium_welfare_language_eq_threeDM])

end PricingWithTips

theorem solution :
    PricingWithTips.NPHardMarketPredicate
      PricingWithTips.EquilibriumWelfareYes :=
  PricingWithTips.equilibrium_welfare_np_hard_of_threeDM_np_hard
    PricingWithTips.threeDM_np_hard

-- Prove2me | solution 1 for PricingWithTips.theorem_5_2_without_tip_unbounded_loss
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T19:57:48.635164+00:00
-- url     : https://prove2.me/submissions/5af99019-bc82-4725-a74e-4ad825429fa7

import Definitions.Def_PricingWithTips_Model

open PricingWithTips

set_option maxRecDepth 10000

private def badMarket (K : ℝ) (hK : 0 < K) : Market (Fin 2) (Fin 1) (Fin 2) where
  value b _ := if b = 0 then 1 else K + 2
  cost d b _ := (if b = 0 then 0 else 2 * K + 2) + d.val
  value_nonneg := by
    intro b s
    fin_cases b <;> norm_num <;> linarith
  cost_nonneg := by
    intro d b s
    fin_cases d <;> fin_cases b <;> norm_num <;> linarith

private def goodAssigned (b : Fin 2) : Option (Fin 1 × Fin 2) :=
  if b = 0 then some (0, 0) else none

private def goodAllocation : Allocation (Fin 2) (Fin 1) (Fin 2) where
  assigned := goodAssigned
  store_unique := by
    intro b₁ b₂ s d₁ d₂ h₁ h₂
    fin_cases b₁ <;> fin_cases b₂ <;> simp_all [goodAssigned]
  courier_unique := by
    intro b₁ b₂ s₁ s₂ d h₁ h₂
    fin_cases b₁ <;> fin_cases b₂ <;> simp_all [goodAssigned]

private def badAssigned (b : Fin 2) : Option (Fin 1 × Fin 2) :=
  if b = 1 then some (0, 0) else none

private def badAllocation : Allocation (Fin 2) (Fin 1) (Fin 2) where
  assigned := badAssigned
  store_unique := by
    intro b₁ b₂ s d₁ d₂ h₁ h₂
    fin_cases b₁ <;> fin_cases b₂
    · simp [badAssigned] at h₁
    · simp [badAssigned] at h₁
    · simp [badAssigned] at h₂
    · rfl
  courier_unique := by
    intro b₁ b₂ s₁ s₂ d h₁ h₂
    fin_cases b₁ <;> fin_cases b₂
    · simp [badAssigned] at h₁
    · simp [badAssigned] at h₁
    · simp [badAssigned] at h₂
    · rfl

private lemma goodAllocation_optimal (K : ℝ) (hK : 0 < K) :
    IsWelfareOptimal (badMarket K hK) goodAllocation := by
  intro A
  have hgood : welfare (badMarket K hK) goodAllocation = 1 := by
    simp [welfare, goodAllocation, goodAssigned, badMarket]
  rw [hgood]
  unfold welfare
  rw [Fin.sum_univ_two]
  cases h0 : A.assigned 0 with
  | none =>
      cases h1 : A.assigned 1 with
      | none => simp
      | some sd1 =>
          rcases sd1 with ⟨s1, d1⟩
          fin_cases s1
          fin_cases d1 <;> simp [badMarket] <;> linarith
  | some sd0 =>
      rcases sd0 with ⟨s0, d0⟩
      fin_cases s0
      fin_cases d0 <;>
        cases h1 : A.assigned 1 with
        | none => simp [badMarket]
        | some sd1 =>
            rcases sd1 with ⟨s1, d1⟩
            fin_cases s1
            fin_cases d1 <;> simp [badMarket] <;> linarith

private lemma badAllocation_equilibrium (K : ℝ) (hK : 0 < K) :
    IsWithoutTipEquilibrium (badMarket K hK) badAllocation
      (fun _ => K + 2) (fun b _ => if b = 1 then 2 * K + 2 else 0) := by
  unfold IsWithoutTipEquilibrium
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    fin_cases s
    linarith
  · intro b s
    fin_cases b <;> fin_cases s <;> simp <;> linarith
  · intro b
    fin_cases b <;> simp [badAllocation, badAssigned, badMarket] <;> linarith
  · intro d b s htrade
    have hd : d = 0 := by
      fin_cases d <;> fin_cases b <;> fin_cases s <;>
        simp [Allocation.Trades, badAllocation, badAssigned] at htrade ⊢
    have hb : b = 1 := by
      fin_cases b <;> fin_cases d <;> fin_cases s <;>
        simp [Allocation.Trades, badAllocation, badAssigned] at htrade ⊢
    subst d
    subst b
    fin_cases s
    constructor
    · simp [badMarket]
    · intro b' s'
      fin_cases b' <;> fin_cases s' <;> simp [badMarket] <;> linarith
  · intro d hd b s
    fin_cases d <;> fin_cases b <;> fin_cases s <;>
      simp [Allocation.CourierWorks, Allocation.Trades, badAllocation, badMarket] at hd ⊢ <;> linarith
  · intro s hs
    fin_cases s
    exfalso
    apply hs
    exact ⟨1, 0, by simp [Allocation.Trades, badAllocation, badAssigned]⟩
  · intro b s hnot
    fin_cases b <;> fin_cases s <;>
      simp [Allocation.Delivers, Allocation.Trades, badAllocation, badAssigned] at hnot ⊢

private lemma every_equilibrium_is_bad (K : ℝ) (hK : 0 < K)
    (A : Allocation (Fin 2) (Fin 1) (Fin 2)) (p : Fin 1 → ℝ)
    (w : Fin 2 → Fin 1 → ℝ)
    (hEq : IsWithoutTipEquilibrium (badMarket K hK) A p w) :
    A.assigned 0 = none ∧ A.assigned 1 = some (0, 0) := by
  rcases hEq with ⟨hp, hw, hbuyers, hworking, hidle, hstores, hundelivered⟩
  cases h0 : A.assigned 0 with
  | none =>
      cases h1 : A.assigned 1 with
      | none =>
          have hunsold : ¬ A.Sells 0 := by
            intro hs
            rcases hs with ⟨b, d, htrade⟩
            fin_cases b <;> simp [Allocation.Trades, h0, h1] at htrade
          have hp0 : p 0 = 0 := hstores 0 hunsold
          have hb0 := hbuyers 0
          simp [h0, badMarket, hp0] at hb0
          exfalso
          linarith
      | some sd =>
          rcases sd with ⟨s, d⟩
          fin_cases s
          fin_cases d
          · exact ⟨rfl, rfl⟩
          · have htrade1 : A.Trades 1 0 1 := h1
            have hwork1 := hworking 1 1 0 htrade1
            have hnot0 : ¬ A.CourierWorks 0 := by
              intro hw0
              rcases hw0 with ⟨b, s, htrade0⟩
              fin_cases b
              · simp [Allocation.Trades, h0] at htrade0
              · fin_cases s
                change A.assigned 1 = some (0, 0) at htrade0
                rw [h1] at htrade0
                simp at htrade0
            have hidle0 := hidle 0 hnot0 1 0
            simp [badMarket] at hwork1 hidle0
            linarith
  | some sd0 =>
      rcases sd0 with ⟨s0, d0⟩
      fin_cases s0
      cases h1 : A.assigned 1 with
      | none =>
          have hb0 := hbuyers 0
          have hb1 := hbuyers 1
          simp [h0, h1, badMarket] at hb0 hb1
          linarith
      | some sd1 =>
          rcases sd1 with ⟨s1, d1⟩
          fin_cases s1
          have hs : (0 : Fin 2) = 1 := A.store_unique h0 h1
          norm_num at hs

theorem solution : ArbitrarilyLowWithoutTipWelfare := by
  intro K hK
  refine ⟨badMarket K hK, ?_, ?_, ?_, ?_⟩
  · left
    refine ⟨(fun b _ => if b = 0 then 0 else 2 * K + 2), (fun d _ => d.val), ?_⟩
    intro d b s
    fin_cases d <;> fin_cases b <;> fin_cases s <;> simp [badMarket] <;> ring
  · refine ⟨goodAllocation, goodAllocation_optimal K hK, ?_⟩
    simp [welfare, goodAllocation, goodAssigned, badMarket]
  · exact ⟨badAllocation, (fun _ => K + 2),
      (fun b _ => if b = 1 then 2 * K + 2 else 0), badAllocation_equilibrium K hK⟩
  · intro A p w hEq
    obtain ⟨h0, h1⟩ := every_equilibrium_is_bad K hK A p w hEq
    simp [welfare, h0, h1, badMarket]
    ring_nf
    exact le_rfl


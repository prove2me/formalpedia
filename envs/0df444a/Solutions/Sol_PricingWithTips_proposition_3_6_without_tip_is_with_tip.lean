-- Prove2me | solution 1 for PricingWithTips.proposition_3_6_without_tip_is_with_tip
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T19:41:47.074068+00:00
-- url     : https://prove2.me/submissions/d2e79b85-7d68-41c7-aade-a161c8f5f1ca

import Definitions.Def_PricingWithTips_Model

open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

private lemma minimumTip_nonneg
    (M : Market B S D) (w t : B → S → ℝ) (b : B) (s : S) :
    0 ≤ minimumTip M w t b s := by
  unfold minimumTip
  apply Real.sInf_nonneg
  intro x hx
  exact hx.1

private lemma minimumTip_zero_of_accepts
    (M : Market B S D) (w t : B → S → ℝ) (b : B) (s : S) (d : D)
    (haccepts : CourierAccepts M w t b s 0 d) :
    minimumTip M w t b s = 0 := by
  apply le_antisymm
  · apply csInf_le
    · exact ⟨0, by intro x hx; exact hx.1⟩
    · exact ⟨le_rfl, d, haccepts⟩
  · exact minimumTip_nonneg M w t b s

theorem solution
    (M : Market B S D) (A : Allocation B S D) (p : S → ℝ) (w : B → S → ℝ)
    (h : IsWithoutTipEquilibrium M A p w) :
    IsWithTipEquilibrium M A p w (fun _ _ => 0) := by
  rcases h with ⟨hp, hw, hbuyers, hworking, hidle, hstores, hundelivered⟩
  refine ⟨hp, hw, ?_, ?_, ?_, ?_, hstores, ?_⟩
  · intro b s
    exact le_rfl
  · intro b
    specialize hbuyers b
    cases hA : A.assigned b with
    | none =>
        simp only [hA] at hbuyers ⊢
        intro s
        have hmin := minimumTip_nonneg M w (fun _ _ => 0) b s
        linarith [hbuyers s]
    | some sd =>
        rcases sd with ⟨s, d⟩
        simp only [hA] at hbuyers ⊢
        have htrade : A.Trades b s d := hA
        have hd := hworking d b s htrade
        have haccepts : CourierAccepts M w (fun _ _ => 0) b s 0 d := by
          constructor
          · simpa using hd.1
          · intro b' s'
            simpa [counterfactualTip] using hd.2 b' s'
        have hmin0 : minimumTip M w (fun _ _ => 0) b s = 0 :=
          minimumTip_zero_of_accepts M w (fun _ _ => 0) b s d haccepts
        refine ⟨?_, ?_, ?_⟩
        · exact hmin0.symm
        · simpa [hmin0] using hbuyers.1
        · intro s'
          have hmin' := minimumTip_nonneg M w (fun _ _ => 0) b s'
          rw [hmin0]
          linarith [hbuyers.2 s']
  · intro d b s htrade
    have hd := hworking d b s htrade
    simpa [courierUtility] using hd
  · intro d hd b s
    simpa [courierUtility] using hidle d hd b s
  · intro b s hnot
    exact ⟨hundelivered b s hnot, rfl⟩


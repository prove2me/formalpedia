-- Prove2me | solution 1 for PricingWithTips.assigned_order_courier_envelope
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:23:24.627788+00:00
-- url     : https://prove2.me/submissions/2654c52d-6ff4-4d0c-9d80-5348d073e691

import Definitions.Def_PricingWithTips_Model

open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

private theorem realized_eq_trade
    (M : Market B S D) (A : Allocation B S D) (w : B → S → ℝ)
    {d : D} {b : B} {s : S} (ht : A.Trades b s d) :
    courierRealizedUtility M A w d = w b s - M.cost d b s := by
  classical
  have hwork : ∃ b' s', A.Trades b' s' d := ⟨b,s,ht⟩
  unfold courierRealizedUtility
  rw [dif_pos hwork]
  let b₀ := Classical.choose hwork
  let hs := Classical.choose_spec hwork
  let s₀ := Classical.choose hs
  have ht₀ : A.Trades b₀ s₀ d := Classical.choose_spec hs
  have hb : b₀ = b := A.courier_unique ht₀ ht
  have ht₀' : A.Trades b s₀ d := by simpa only [hb] using ht₀
  have hpair : (s₀,d) = (s,d) := Option.some.inj (ht₀'.symm.trans ht)
  have hss : s₀ = s := congrArg Prod.fst hpair
  change w b₀ s₀ - M.cost d b₀ s₀ = w b s - M.cost d b s
  rw [hb,hss]

private theorem realized_eq_idle
    (M : Market B S D) (A : Allocation B S D) (w : B → S → ℝ)
    (d : D) (hd : ¬ A.CourierWorks d) :
    courierRealizedUtility M A w d = 0 := by
  classical
  change ¬ ∃ b s, A.Trades b s d at hd
  simp [courierRealizedUtility, hd]

theorem solution [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (w : B → S → ℝ) (uBar : D → ℝ)
    (hplan : IsCourierPlanFor M A w)
    (hreal : ∀ d, courierRealizedUtility M A w d = uBar d)
    {b : B} {s : S} {d : D} (ht : A.Trades b s d) :
    (⨅ d' : D, M.cost d' b s + uBar d') = w b s := by
  classical
  have hupper : ∀ d' b' s', w b' s' - M.cost d' b' s' ≤ uBar d' := by
    intro d' b' s'
    by_cases hd' : A.CourierWorks d'
    · obtain ⟨b₀,s₀,ht₀⟩ := hd'
      have h := (hplan.2.1 d' b₀ s₀ ht₀).2 b' s'
      rw [← hreal d', realized_eq_trade M A w ht₀]
      exact h
    · have h := hplan.2.2.1 d' hd' b' s'
      rw [← hreal d', realized_eq_idle M A w d' hd']
      exact h
  apply le_antisymm
  · have hchosen : M.cost d b s + uBar d = w b s := by
      rw [← hreal d, realized_eq_trade M A w ht]
      ring
    rw [← hchosen]
    exact ciInf_le (Finite.bddBelow_range _) d
  · apply le_ciInf
    intro d'
    linarith [hupper d' b s]

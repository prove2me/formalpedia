-- Prove2me | solution 1 for PricingWithTips.proposition_3_7_zero_tip_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-21T02:57:56.814675+00:00
-- url     : https://prove2.me/submissions/3dbe4baf-f8e1-43ea-8ee5-b5e21b0d091f

import Theorems.Thm_PricingWithTips_lemma_A_1_minimum_tip_formula

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

private theorem minimumTip_le_shift_off [Nonempty D]
    (M : Market B S D) (w t : B → S → ℝ)
    (htnonneg : ∀ b s, 0 ≤ t b s) (b : B) (s : S)
    (hzero : t b s = 0) :
    minimumTip M w t b s ≤
      minimumTip M (fun b s => w b s + t b s) (fun _ _ => 0) b s := by
  letI : Nonempty B := ⟨b⟩
  letI : Nonempty S := ⟨s⟩
  rw [lemma_A_1_minimum_tip_formula M w t b s,
    lemma_A_1_minimum_tip_formula M (fun b s => w b s + t b s)
      (fun _ _ => 0) b s]
  unfold minimumTipFormula
  apply le_ciInf
  intro d
  apply le_trans (ciInf_le (Finite.bddBelow_range _) d)
  apply max_le_max le_rfl
  apply max_le_max
  · simp [hzero]
  · apply ciSup_le
    intro b'
    apply le_trans ?_ (le_ciSup (Finite.bddAbove_range _) b')
    apply ciSup_le
    intro s'
    apply le_trans ?_ (le_ciSup (Finite.bddAbove_range _) s')
    by_cases hpair : (b', s') = (b, s)
    · simp [hpair]
    · simp only [if_neg hpair]
      by_cases hbb : b' = b
      · subst b'
        simp [hzero]
        linarith [htnonneg b s']
      · simp [hbb, hzero]

private theorem minimumTip_zero_shift_trade [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (w t : B → S → ℝ)
    (hcourier : ∀ d b s, A.Trades b s d →
      0 ≤ courierUtility M w t d b s ∧
      ∀ b' s', courierUtility M w t d b' s' ≤ courierUtility M w t d b s)
    {b : B} {s : S} {d : D} (ht : A.Trades b s d) :
    minimumTip M (fun b s => w b s + t b s) (fun _ _ => 0) b s = 0 := by
  classical
  let w' : B → S → ℝ := fun b s => w b s + t b s
  let T : Set ℝ := {τ | 0 ≤ τ ∧ ∃ d, CourierAccepts M w' (fun _ _ => 0) b s τ d}
  have haccept : CourierAccepts M w' (fun _ _ => 0) b s 0 d := by
    constructor
    · simpa [w', courierUtility] using (hcourier d b s ht).1
    · intro b' s'
      simpa [w', courierUtility, counterfactualTip] using
        (hcourier d b s ht).2 b' s'
  have hzero : (0 : ℝ) ∈ T := ⟨le_refl _, d, haccept⟩
  change sInf T = 0
  apply le_antisymm
  · exact csInf_le ⟨0, fun τ hτ => hτ.1⟩ hzero
  · exact le_csInf ⟨0, hzero⟩ (fun τ hτ => hτ.1)

theorem zero_tip_equivalence_nonempty [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (p : S → ℝ) (w t : B → S → ℝ)
    (heq : IsWithTipEquilibrium M A p w t) :
    IsWithTipEquilibrium M A p (fun b s => w b s + t b s)
      (fun _ _ => 0) := by
  classical
  rcases heq with ⟨hp,hw,ht,hbuyer,hcourier,hidle,hunsold,hoff⟩
  refine ⟨hp, ?_, ?_, ?_, ?_, ?_, hunsold, ?_⟩
  · intro b s
    linarith [hw b s, ht b s]
  · intro b s
    exact le_refl _
  · intro b
    cases ha : A.assigned b with
    | none =>
        have hb := hbuyer b
        simp only [ha] at hb ⊢
        intro s
        have hd : ¬ A.Delivers b s := by
          rintro ⟨d,hd⟩
          change A.assigned b = some (s,d) at hd
          rw [ha] at hd
          cases hd
        have htzero := (hoff b s hd).2
        have hmin := minimumTip_le_shift_off M w t ht b s htzero
        linarith [hb s]
    | some sd =>
        rcases sd with ⟨s₀,d₀⟩
        have hb := hbuyer b
        simp only [ha] at hb ⊢
        have htrade : A.Trades b s₀ d₀ := ha
        have htip₀ := hb.1
        have hmin₀ := minimumTip_zero_shift_trade M A w t hcourier htrade
        constructor
        · exact hmin₀.symm
        constructor
        · rw [hmin₀]
          linarith [hb.2.1, ht b s₀]
        · intro s'
          by_cases hsame : s' = s₀
          · subst s'
            exact le_refl _
          · have hd : ¬ A.Delivers b s' := by
              rintro ⟨d,hd⟩
              have hp : (s₀,d₀) = (s',d) := Option.some.inj (ha.symm.trans hd)
              exact hsame (congrArg Prod.fst hp).symm
            have htzero := (hoff b s' hd).2
            have hmin := minimumTip_le_shift_off M w t ht b s' htzero
            have hbuyer_alt := hb.2.2 s'
            rw [← htip₀] at hbuyer_alt
            rw [hmin₀]
            linarith [hbuyer_alt, ht b s₀]
  · intro d b s htrade
    simpa [courierUtility] using hcourier d b s htrade
  · intro d hid b s
    simpa [courierUtility] using hidle d hid b s
  · intro b s hd
    have h := hoff b s hd
    simp [h.1,h.2]

end PricingWithTips

open PricingWithTips

theorem solution {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
    [DecidableEq B] [DecidableEq S] [DecidableEq D]
    (M : Market B S D) (A : Allocation B S D)
    (h : HasWithTipEquilibriumAt M A) :
    ∃ p w, IsWithTipEquilibrium M A p w (fun _ _ => 0) := by
  classical
  obtain ⟨p,w,t,heq⟩ := h
  by_cases hD : Nonempty D
  · letI : Nonempty D := hD
    exact ⟨p, (fun b s => w b s + t b s),
      zero_tip_equivalence_nonempty M A p w t heq⟩
  · have hnone : ∀ b s, ¬ A.Delivers b s := by
      intro b s ⟨d,_⟩
      exact hD ⟨d⟩
    have htzero : t = (fun _ _ => 0) := by
      funext b s
      exact (heq.2.2.2.2.2.2.2 b s (hnone b s)).2
    exact ⟨p,w,by simpa [htzero] using heq⟩

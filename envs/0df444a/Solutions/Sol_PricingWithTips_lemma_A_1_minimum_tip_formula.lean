-- Prove2me | solution 1 for PricingWithTips.lemma_A_1_minimum_tip_formula
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T19:41:48.005243+00:00
-- url     : https://prove2.me/submissions/5d9df1f4-0a13-4a1c-bda5-1c91774e5297

import Definitions.Def_PricingWithTips_Model

open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

private noncomputable def deviationThreshold
    (M : Market B S D) (w t : B → S → ℝ) (b : B) (s : S) (d : D) : ℝ :=
  max 0 (max (M.cost d b s - w b s)
    (⨆ (b' : B) (s' : S), if (b', s') = (b, s) then 0 else
      w b' s' + (if b' = b then 0 else t b' s') - M.cost d b' s' - w b s + M.cost d b s))

private lemma accepts_iff_threshold_le
    (M : Market B S D) (w t : B → S → ℝ) (b : B) (s : S)
    (τ : ℝ) (d : D) :
    (0 ≤ τ ∧ CourierAccepts M w t b s τ d) ↔
      deviationThreshold M w t b s d ≤ τ := by
  letI : Nonempty B := ⟨b⟩
  letI : Nonempty S := ⟨s⟩
  constructor
  · rintro ⟨hτ, hpart, hpref⟩
    unfold deviationThreshold
    apply max_le hτ
    apply max_le
    · linarith
    · apply ciSup_le
      intro b'
      apply ciSup_le
      intro s'
      by_cases hpair : (b', s') = (b, s)
      · simp [hpair, hτ]
      · have hcomp := hpref b' s'
        simp only [counterfactualTip] at hcomp
        simp only [hpair, if_false]
        by_cases hb : b' = b
        · subst b'
          simp only [if_pos rfl] at hcomp ⊢
          by_cases hs : s' = s
          · subst s'
            exact (hpair rfl).elim
          · simp only [hs, if_false] at hcomp
            linarith
        · simp only [hb, if_false] at hcomp ⊢
          linarith
  · intro hthreshold
    have hτ : 0 ≤ τ := le_trans (le_max_left _ _) hthreshold
    have hinner :
        max (M.cost d b s - w b s)
          (⨆ (b' : B) (s' : S), if (b', s') = (b, s) then 0 else
            w b' s' + (if b' = b then 0 else t b' s') - M.cost d b' s' - w b s + M.cost d b s) ≤ τ :=
      le_trans (le_max_right _ _) hthreshold
    have hpartbound : M.cost d b s - w b s ≤ τ :=
      le_trans (le_max_left _ _) hinner
    have hsupbound :
        (⨆ (b' : B) (s' : S), if (b', s') = (b, s) then 0 else
          w b' s' + (if b' = b then 0 else t b' s') - M.cost d b' s' - w b s + M.cost d b s) ≤ τ :=
      le_trans (le_max_right _ _) hinner
    refine ⟨hτ, ?_, ?_⟩
    · linarith
    · intro b' s'
      by_cases hpair : (b', s') = (b, s)
      · rcases hpair with ⟨rfl, rfl⟩
        simp [counterfactualTip]
      · have hle1 :
            (if (b', s') = (b, s) then 0 else
              w b' s' + (if b' = b then 0 else t b' s') - M.cost d b' s' - w b s + M.cost d b s) ≤
              (⨆ s'' : S, if (b', s'') = (b, s) then 0 else
                w b' s'' + (if b' = b then 0 else t b' s'') - M.cost d b' s'' - w b s + M.cost d b s) :=
          le_ciSup (Finite.bddAbove_range
            (fun s'' : S => if (b', s'') = (b, s) then 0 else
              w b' s'' + (if b' = b then 0 else t b' s'') - M.cost d b' s'' - w b s + M.cost d b s)) s'
        have hle2 :
            (⨆ s'' : S, if (b', s'') = (b, s) then 0 else
              w b' s'' + (if b' = b then 0 else t b' s'') - M.cost d b' s'' - w b s + M.cost d b s) ≤
              (⨆ (b'' : B) (s'' : S), if (b'', s'') = (b, s) then 0 else
                w b'' s'' + (if b'' = b then 0 else t b'' s'') - M.cost d b'' s'' - w b s + M.cost d b s) :=
          le_ciSup (Finite.bddAbove_range
            (fun b'' : B => ⨆ s'' : S, if (b'', s'') = (b, s) then 0 else
              w b'' s'' + (if b'' = b then 0 else t b'' s'') - M.cost d b'' s'' - w b s + M.cost d b s)) b'
        have halt :
            w b' s' + (if b' = b then 0 else t b' s') - M.cost d b' s' - w b s + M.cost d b s ≤ τ := by
          simpa [hpair] using le_trans (le_trans hle1 hle2) hsupbound
        simp only [counterfactualTip]
        by_cases hb : b' = b
        · subst b'
          simp only [if_pos rfl] at halt ⊢
          by_cases hs : s' = s
          · subst s'
            exact (hpair rfl).elim
          · simp only [hs, if_false]
            linarith
        · simp only [hb, if_false] at halt ⊢
          linarith

theorem solution [Nonempty D]
    (M : Market B S D) (w t : B → S → ℝ) (b : B) (s : S) :
    minimumTip M w t b s = minimumTipFormula M w t b s := by
  let T : D → ℝ := deviationThreshold M w t b s
  have hfeasible : ∀ τ : ℝ,
      (0 ≤ τ ∧ ∃ d, CourierAccepts M w t b s τ d) ↔ ∃ d, T d ≤ τ := by
    intro τ
    constructor
    · rintro ⟨hτ, d, hd⟩
      exact ⟨d, (accepts_iff_threshold_le M w t b s τ d).1 ⟨hτ, hd⟩⟩
    · rintro ⟨d, hd⟩
      rcases (accepts_iff_threshold_le M w t b s τ d).2 hd with ⟨hτ, haccepts⟩
      exact ⟨hτ, d, haccepts⟩
  have hset : {τ : ℝ | 0 ≤ τ ∧ ∃ d, CourierAccepts M w t b s τ d} =
      {τ : ℝ | ∃ d, T d ≤ τ} := by
    ext τ
    exact hfeasible τ
  have hTnonneg : ∀ d, 0 ≤ T d := by
    intro d
    exact le_max_left _ _
  have hbddT : BddBelow (Set.range T) :=
    ⟨0, by rintro _ ⟨d, rfl⟩; exact hTnonneg d⟩
  have hA_nonempty : ({τ : ℝ | ∃ d, T d ≤ τ}).Nonempty := by
    let d : D := Classical.choice inferInstance
    exact ⟨T d, d, le_rfl⟩
  have hbddA : BddBelow {τ : ℝ | ∃ d, T d ≤ τ} := by
    refine ⟨0, ?_⟩
    rintro τ ⟨d, hd⟩
    exact le_trans (hTnonneg d) hd
  unfold minimumTip minimumTipFormula
  rw [hset]
  change sInf {τ : ℝ | ∃ d, T d ≤ τ} = ⨅ d, T d
  apply le_antisymm
  · apply le_ciInf
    intro d
    exact csInf_le hbddA ⟨d, le_rfl⟩
  · apply le_csInf hA_nonempty
    intro τ hτ
    rcases hτ with ⟨d, hd⟩
    exact le_trans (ciInf_le hbddT d) hd


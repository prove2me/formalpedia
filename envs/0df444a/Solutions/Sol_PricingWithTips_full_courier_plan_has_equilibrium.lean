-- Prove2me | solution 1 for PricingWithTips.full_courier_plan_has_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T20:32:43.068564+00:00
-- url     : https://prove2.me/submissions/0f404a31-4c14-42c2-96a2-31013f89621f

import Theorems.Thm_PricingWithTips_lemma_A_1_minimum_tip_formula

open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem solution [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hfull : ∀ d, A.CourierWorks d)
    (w₀ : B → S → ℝ) (hplan : IsCourierPlanFor M A w₀) :
    HasWithTipEquilibriumAt M A := by
  classical
  rcases hplan with ⟨hw₀, hcourier₀, _hidle₀, _hunpaid₀⟩
  obtain ⟨U, hU⟩ : BddAbove (Set.range (fun bs : B × S => M.value bs.1 bs.2)) :=
    Finite.bddAbove_range _
  let K : ℝ := max 0 U + 1
  have hKpos : 0 < K := by dsimp [K]; linarith [le_max_left (0 : ℝ) U]
  have hKval : ∀ b s, M.value b s < K := by
    intro b s
    have hv : M.value b s ≤ U := hU ⟨(b, s), rfl⟩
    have hUmax : U ≤ max 0 U := le_max_right _ _
    dsimp [K]
    linarith
  let w : B → S → ℝ := fun b s => if A.Delivers b s then w₀ b s + K else 0
  have hw : ∀ b s, 0 ≤ w b s := by
    intro b s
    by_cases hd : A.Delivers b s
    · simp only [w, if_pos hd]
      linarith [hw₀ b s]
    · simp [w, hd]
  have hcourier : ∀ d b s, A.Trades b s d →
      0 ≤ w b s - M.cost d b s ∧
      ∀ b' s', w b' s' - M.cost d b' s' ≤ w b s - M.cost d b s := by
    intro d b s htrade
    have hdel : A.Delivers b s := ⟨d, htrade⟩
    have hwbs : w b s = w₀ b s + K := dif_pos hdel
    have hbase := hcourier₀ d b s htrade
    constructor
    · rw [hwbs]
      linarith [hbase.1]
    · intro b' s'
      by_cases hdel' : A.Delivers b' s'
      · rw [hwbs]
        simp only [w, if_pos hdel']
        linarith [hbase.2 b' s']
      · rw [hwbs]
        simp only [w, if_neg hdel']
        linarith [M.cost_nonneg d b' s', hbase.1]
  have hunpaid : ∀ b s, ¬ A.Delivers b s → w b s = 0 := by
    intro b s hnot
    exact dif_neg hnot
  have hmin_nonneg : ∀ b s, 0 ≤ minimumTip M w (fun _ _ => 0) b s := by
    intro b s
    rw [lemma_A_1_minimum_tip_formula]
    unfold minimumTipFormula
    apply le_ciInf
    intro d
    exact le_max_left _ _
  have hmin_on : ∀ d b s, A.Trades b s d →
      minimumTip M w (fun _ _ => 0) b s = 0 := by
    intro d b s htrade
    let T : Set ℝ := {τ | 0 ≤ τ ∧ ∃ d, CourierAccepts M w (fun _ _ => 0) b s τ d}
    have hT_bdd : BddBelow T := by
      refine ⟨0, ?_⟩
      rintro τ ⟨hτ, _⟩
      exact hτ
    have hzero : (0 : ℝ) ∈ T := by
      refine ⟨le_refl _, d, ?_⟩
      rcases hcourier d b s htrade with ⟨hpart, hpref⟩
      constructor
      · simpa using hpart
      · intro b' s'
        simpa [counterfactualTip] using hpref b' s'
    have hupper : minimumTip M w (fun _ _ => 0) b s ≤ 0 := by
      change sInf T ≤ 0
      exact csInf_le hT_bdd hzero
    exact le_antisymm hupper (hmin_nonneg b s)
  have hmin_off : ∀ b s, ¬ A.Delivers b s →
      K ≤ minimumTip M w (fun _ _ => 0) b s := by
    intro b s hnot
    rw [lemma_A_1_minimum_tip_formula]
    unfold minimumTipFormula
    apply le_ciInf
    intro d
    obtain ⟨b', s', htrade⟩ := hfull d
    have hdel' : A.Delivers b' s' := ⟨d, htrade⟩
    have hneq : (b', s') ≠ (b, s) := by
      rintro ⟨rfl, rfl⟩
      exact hnot hdel'
    let g : B → S → ℝ := fun x y =>
      if (x, y) = (b, s) then 0 else
        w x y + (if x = b then 0 else (0 : B → S → ℝ) x y) -
          M.cost d x y - w b s + M.cost d b s
    have hterm_le : g b' s' ≤ ⨆ (x : B) (y : S), g x y := by
      have h₁ : g b' s' ≤ ⨆ y : S, g b' y :=
        le_ciSup (Finite.bddAbove_range (g b')) s'
      have h₂ : (⨆ y : S, g b' y) ≤ ⨆ x : B, (⨆ y : S, g x y) :=
        le_ciSup (Finite.bddAbove_range (fun x : B => ⨆ y : S, g x y)) b'
      exact le_trans h₁ h₂
    have hterm : g b' s' = w₀ b' s' + K - M.cost d b' s' + M.cost d b s := by
      change (if (b', s') = (b, s) then 0 else
        w b' s' + (if b' = b then 0 else (0 : B → S → ℝ) b' s') -
          M.cost d b' s' - w b s + M.cost d b s) = _
      rw [if_neg hneq]
      simp [w, hdel', hnot]
    have hlow : K ≤ g b' s' := by
      rw [hterm]
      linarith [(hcourier₀ d b' s' htrade).1, M.cost_nonneg d b s]
    have hsup : K ≤ ⨆ (x : B) (y : S), g x y := le_trans hlow hterm_le
    have hbound : K ≤ max 0 (max (M.cost d b s - w b s) (⨆ (x : B) (y : S), g x y)) :=
      le_trans hsup (le_trans (le_max_right _ _) (le_max_right _ _))
    simpa [g] using hbound
  refine ⟨fun _ => 0, w, fun _ _ => 0, ?_⟩
  refine ⟨by simp, hw, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    cases hba : A.assigned b with
    | none =>
      simp only [hba]
      intro s
      have hnot : ¬ A.Delivers b s := by
        rintro ⟨d, hd⟩
        simp [Allocation.Trades, hba] at hd
      have htip := hmin_off b s hnot
      have hval := hKval b s
      simp
      linarith
    | some sd =>
      rcases sd with ⟨s₀, d₀⟩
      simp only [hba]
      have htrade : A.Trades b s₀ d₀ := hba
      have htip₀ := hmin_on d₀ b s₀ htrade
      refine ⟨by simpa [htip₀], ?_, ?_⟩
      · simpa [htip₀] using M.value_nonneg b s₀
      · intro s'
        by_cases hs : s' = s₀
        · subst s'
          exact le_refl _
        · have hnot : ¬ A.Delivers b s' := by
            rintro ⟨d, hd⟩
            have hp : (s₀, d₀) = (s', d) := Option.some.inj (hba.symm.trans hd)
            exact hs (congrArg Prod.fst hp).symm
          have htip := hmin_off b s' hnot
          have hval := hKval b s'
          simp [htip₀]
          linarith [M.value_nonneg b s₀]
  · intro d b s htrade
    simpa [courierUtility] using hcourier d b s htrade
  · intro d hnot
    exact (hnot (hfull d)).elim
  · intro s hnot
    rfl
  · intro b s hnot
    exact ⟨hunpaid b s hnot, rfl⟩

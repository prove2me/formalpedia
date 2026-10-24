-- Prove2me | solution 1 for PricingWithTips.optimal_empty_has_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T21:35:48.920858+00:00
-- url     : https://prove2.me/submissions/fa025a22-4e63-4782-a0bb-02ec9421c610

import Definitions.Def_PricingWithTips_Model

open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

private theorem empty_allocation_has_equilibrium [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hempty : ∀ b, A.assigned b = none)
    (hdom : ∀ b s d, M.value b s ≤ M.cost d b s) :
    HasWithTipEquilibriumAt M A := by
  classical
  have htip : ∀ b s, M.value b s ≤ minimumTip M (fun _ _ => 0) (fun _ _ => 0) b s := by
    intro b s
    let T : Set ℝ := {τ | 0 ≤ τ ∧ ∃ d, CourierAccepts M (fun _ _ => 0) (fun _ _ => 0) b s τ d}
    have hT_nonempty : T.Nonempty := by
      let d : D := Classical.choice inferInstance
      refine ⟨M.cost d b s, ?_⟩
      constructor
      · exact M.cost_nonneg d b s
      · refine ⟨d, ?_⟩
        constructor
        · simp
        · intro b' s'
          by_cases hb : b' = b
          · subst b'
            by_cases hs : s' = s
            · subst s'
              simp [counterfactualTip]
            · simp [counterfactualTip, hs]
              linarith [M.cost_nonneg d b s']
          · simp [counterfactualTip, hb]
            linarith [M.cost_nonneg d b' s']
    have hT_lower : ∀ τ ∈ T, M.value b s ≤ τ := by
      intro τ hτ
      obtain ⟨_, d, hd⟩ := hτ
      have hcost := hdom b s d
      have haccept := hd.1
      dsimp [CourierAccepts] at hd
      simp only at haccept
      linarith
    change M.value b s ≤ sInf T
    exact le_csInf hT_nonempty hT_lower
  refine ⟨fun _ => 0, fun _ _ => 0, fun _ _ => 0, ?_⟩
  refine ⟨by simp, by simp, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    rw [hempty b]
    intro s
    have hs := htip b s
    simpa using (sub_nonpos.mpr hs)
  · intro d b s htrade
    simp [Allocation.Trades, hempty b] at htrade
  · intro d _ b s
    simp [courierUtility]
    exact M.cost_nonneg d b s
  · intro s _
    rfl
  · intro b s _
    exact ⟨rfl, rfl⟩

private theorem optimal_empty_cost_bound
    (M : Market B S D) (A : Allocation B S D)
    (hempty : ∀ b, A.assigned b = none)
    (hoptimal : IsWelfareOptimal M A) :
    ∀ b s d, M.value b s ≤ M.cost d b s := by
  classical
  intro b s d
  let A' : Allocation B S D := {
    assigned := fun b' => if b' = b then some (s, d) else none
    store_unique := by
      intro b₁ b₂ s' d₁ d₂ h₁ h₂
      by_cases hb₁ : b₁ = b
      · by_cases hb₂ : b₂ = b
        · exact hb₁.trans hb₂.symm
        · simp [hb₂] at h₂
      · simp [hb₁] at h₁
    courier_unique := by
      intro b₁ b₂ s₁ s₂ d' h₁ h₂
      by_cases hb₁ : b₁ = b
      · by_cases hb₂ : b₂ = b
        · exact hb₁.trans hb₂.symm
        · simp [hb₂] at h₂
      · simp [hb₁] at h₁
  }
  have hA_zero : welfare M A = 0 := by
    simp [welfare, hempty]
  have hA'_value : welfare M A' = M.value b s - M.cost d b s := by
    simp only [welfare, A']
    calc
      (∑ x, match if x = b then some (s, d) else none with
        | none => 0
        | some (s', d') => M.value x s' - M.cost d' x s') =
          ∑ x, if x = b then M.value x s - M.cost d x s else 0 := by
            apply Finset.sum_congr rfl
            intro x _
            split_ifs <;> simp_all
      _ = _ := by simp
  have hle := hoptimal A'
  rw [hA_zero, hA'_value] at hle
  linarith

theorem solution [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hempty : ∀ b, A.assigned b = none)
    (hoptimal : IsWelfareOptimal M A) :
    HasWithTipEquilibriumAt M A := by
  exact empty_allocation_has_equilibrium M A hempty
    (optimal_empty_cost_bound M A hempty hoptimal)

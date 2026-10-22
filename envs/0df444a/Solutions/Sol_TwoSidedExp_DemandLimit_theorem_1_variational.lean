-- Prove2me | solution 1 for TwoSidedExp.DemandLimit.theorem_1_variational
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T04:40:19.019998+00:00
-- url     : https://prove2.me/submissions/b7dcd3ba-fbbe-4363-a043-93be972f6d7d

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting
import Theorems.Thm_TwoSidedExp_DemandLimit_theorem_1

open Filter Topology MeasureTheory

namespace TSEVarAux

open TwoSidedExp.DemandLimit

/-- Jensen for `log` with an extra constant atom: for `ε > 0`, `c ≥ 0`, `s, s' > 0`, writing
`D = ε + Σ c s`, `D' = ε + Σ c s'`, we have `Σ (c s / D) log (s'/s) ≤ log D' - log D`. -/
theorem jensen_log {Θ : Type} [Fintype Θ] (ε : ℝ) (hε : 0 < ε) (c s s' : Θ → ℝ)
    (hc : ∀ θ, 0 ≤ c θ) (hs : ∀ θ, 0 < s θ) (hs' : ∀ θ, 0 < s' θ) :
    ∑ θ, c θ * s θ / (ε + ∑ θ', c θ' * s θ') * Real.log (s' θ / s θ)
      ≤ Real.log (ε + ∑ θ, c θ * s' θ) - Real.log (ε + ∑ θ, c θ * s θ) := by
  set D := ε + ∑ θ', c θ' * s θ' with hD
  have hDpos : 0 < D := by
    have : 0 ≤ ∑ θ', c θ' * s θ' :=
      Finset.sum_nonneg (fun θ _ => mul_nonneg (hc θ) (hs θ).le)
    linarith
  have hD'pos : 0 < ε + ∑ θ, c θ * s' θ := by
    have : 0 ≤ ∑ θ', c θ' * s' θ' :=
      Finset.sum_nonneg (fun θ _ => mul_nonneg (hc θ) (hs' θ).le)
    linarith
  let w : Option Θ → ℝ := fun o => Option.elim o (ε / D) (fun θ => c θ * s θ / D)
  let p : Option Θ → ℝ := fun o => Option.elim o 1 (fun θ => s' θ / s θ)
  have h0 : ∀ i ∈ (Finset.univ : Finset (Option Θ)), 0 ≤ w i := by
    intro i _
    cases i with
    | none => exact div_nonneg hε.le hDpos.le
    | some θ => exact div_nonneg (mul_nonneg (hc θ) (hs θ).le) hDpos.le
  have h1 : ∑ i ∈ (Finset.univ : Finset (Option Θ)), w i = 1 := by
    rw [Fintype.sum_option]
    simp only [w, Option.elim]
    rw [← Finset.sum_div, ← add_div, ← hD]
    exact div_self hDpos.ne'
  have hmem : ∀ i ∈ (Finset.univ : Finset (Option Θ)), p i ∈ Set.Ioi (0 : ℝ) := by
    intro i _
    cases i with
    | none => exact Set.mem_Ioi.mpr one_pos
    | some θ => exact Set.mem_Ioi.mpr (div_pos (hs' θ) (hs θ))
  have hJ := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum h0 h1 hmem
  rw [Fintype.sum_option, Fintype.sum_option] at hJ
  simp only [w, p, Option.elim, smul_eq_mul, Real.log_one, mul_zero, zero_add] at hJ
  have hsum : ε / D * 1 + ∑ θ, c θ * s θ / D * (s' θ / s θ)
      = (ε + ∑ θ, c θ * s' θ) / D := by
    rw [mul_one, add_div, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl (fun θ _ => ?_)
    have := (hs θ).ne'
    field_simp
  rw [hsum, Real.log_div hD'pos.ne' hDpos.ne'] at hJ
  exact hJ

/-- Key inequality: if `s > 0` satisfies the steady-state equations, then for every `s' > 0`,
`W(s') - W(s) ≥ Σ τ ν s (s'/s - 1 - log(s'/s))`. -/
theorem W_lower {Γ Θ : Type} [Fintype Γ] [Fintype Θ] (S : MFSystem Γ Θ) (lam tau : ℝ)
    (hlam : 0 ≤ lam) (hφ : ∀ γ, 0 ≤ S.φ γ) (hc : ∀ γ θ, 0 ≤ S.α γ θ * S.v γ θ)
    (heps : ∀ γ, 0 < S.eps γ) (s s' : Θ → ℝ) (hs : ∀ θ, 0 < s θ) (hs' : ∀ θ, 0 < s' θ)
    (hst : ∀ θ, (S.ρ θ - s θ) * (tau * S.ν θ) = lam * ∑ γ, S.φ γ * S.choice γ θ s) :
    ∑ θ, tau * S.ν θ * s θ * (s' θ / s θ - 1 - Real.log (s' θ / s θ))
      ≤ S.W lam tau s' - S.W lam tau s := by
  -- the customer part
  have hcust : ∀ γ, lam * S.φ γ * ∑ θ, S.choice γ θ s * Real.log (s' θ / s θ)
      ≤ lam * S.φ γ * Real.log (S.eps γ + ∑ θ, S.α γ θ * S.v γ θ * s' θ)
        - lam * S.φ γ * Real.log (S.eps γ + ∑ θ, S.α γ θ * S.v γ θ * s θ) := by
    intro γ
    rw [← mul_sub]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hlam (hφ γ))
    have := jensen_log (S.eps γ) (heps γ) (fun θ => S.α γ θ * S.v γ θ) s s' (hc γ) hs hs'
    simpa [MFSystem.choice] using this
  have hsumc := Finset.sum_le_sum (fun γ (_ : γ ∈ (Finset.univ : Finset Γ)) => hcust γ)
  -- rewrite the left side using the steady-state equation
  have hswap : ∑ γ, lam * S.φ γ * ∑ θ, S.choice γ θ s * Real.log (s' θ / s θ)
      = ∑ θ, (S.ρ θ - s θ) * (tau * S.ν θ) * Real.log (s' θ / s θ) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun θ _ => ?_)
    rw [hst θ, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    ring
  rw [hswap, Finset.sum_sub_distrib] at hsumc
  have hlog : ∀ θ, Real.log (s' θ / s θ) = Real.log (s' θ) - Real.log (s θ) :=
    fun θ => Real.log_div (hs' θ).ne' (hs θ).ne'
  unfold MFSystem.W
  have e1 : ∑ θ, tau * S.ν θ * s θ * (s' θ / s θ - 1 - Real.log (s' θ / s θ))
      = ∑ θ, (S.ρ θ - s θ) * (tau * S.ν θ) * Real.log (s' θ / s θ)
        - (∑ θ, tau * S.ν θ * S.ρ θ * Real.log (s' θ)
            - ∑ θ, tau * S.ν θ * S.ρ θ * Real.log (s θ))
        + (∑ θ, tau * S.ν θ * s' θ - ∑ θ, tau * S.ν θ * s θ) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun θ _ => ?_)
    rw [hlog θ]
    have := (hs θ).ne'
    field_simp
    ring
  rw [e1]
  linarith

theorem term_nonneg (r : ℝ) (hr : 0 < r) : 0 ≤ r - 1 - Real.log r := by
  have := Real.log_le_sub_one_of_pos hr
  linarith

end TSEVarAux

open TwoSidedExp.DemandLimit TSEVarAux in
theorem solution {Γ Θ : Type} [Fintype Γ] [Fintype Θ] (M : Model Γ Θ)
    (hM : M.Standing) (lam tau : ℝ) (hlam : 0 < lam) (htau : 0 < tau) (s : Θ → ℝ) :
    ((∀ θ, 0 < s θ ∧ s θ ≤ M.sys.ρ θ) ∧
        ∀ s' : Θ → ℝ, (∀ θ, 0 < s' θ ∧ s' θ ≤ M.sys.ρ θ) →
          M.sys.W lam tau s ≤ M.sys.W lam tau s') ↔
      M.sys.IsSteady lam tau s := by
  have hφ : ∀ γ, 0 ≤ M.sys.φ γ := fun γ => (hM.phi_pos γ).le
  have hc : ∀ γ θ, 0 ≤ M.sys.α γ θ * M.sys.v γ θ :=
    fun γ θ => mul_nonneg (hM.alpha_pos γ θ).le (hM.v_pos γ θ).le
  obtain ⟨⟨sstar, hsstar, -⟩, hint⟩ := theorem_1 M hM lam tau hlam htau
  have hlow : ∀ t : Θ → ℝ, M.sys.IsSteady lam tau t → ∀ s' : Θ → ℝ, (∀ θ, 0 < s' θ) →
      ∑ θ, tau * M.sys.ν θ * t θ * (s' θ / t θ - 1 - Real.log (s' θ / t θ))
        ≤ M.sys.W lam tau s' - M.sys.W lam tau t := fun t ht s' hs' =>
    W_lower M.sys lam tau hlam.le hφ hc hM.eps_pos t s' (fun θ => (hint t ht θ).1) hs' ht.2
  have hnn : ∀ t : Θ → ℝ, M.sys.IsSteady lam tau t → ∀ s' : Θ → ℝ, (∀ θ, 0 < s' θ) →
      ∀ θ, 0 ≤ tau * M.sys.ν θ * t θ * (s' θ / t θ - 1 - Real.log (s' θ / t θ)) := by
    intro t ht s' hs' θ
    have ht0 := (hint t ht θ).1
    exact mul_nonneg (mul_nonneg (mul_nonneg htau.le (hM.nu_pos θ).le) ht0.le)
      (term_nonneg _ (div_pos (hs' θ) ht0))
  constructor
  · rintro ⟨hfeas, hmin⟩
    have hle := hmin sstar (fun θ => ⟨(hint sstar hsstar θ).1, (hint sstar hsstar θ).2.le⟩)
    have hspos : ∀ θ, 0 < s θ := fun θ => (hfeas θ).1
    have hL := hlow sstar hsstar s hspos
    have hN := hnn sstar hsstar s hspos
    have hsum0 : ∑ θ, tau * M.sys.ν θ * sstar θ *
        (s θ / sstar θ - 1 - Real.log (s θ / sstar θ)) = 0 := by
      apply le_antisymm _ (Finset.sum_nonneg (fun θ _ => hN θ))
      linarith
    have heach := (Finset.sum_eq_zero_iff_of_nonneg (fun θ _ => hN θ)).mp hsum0
    have heq : s = sstar := by
      funext θ
      have h := heach θ (Finset.mem_univ θ)
      have hs0 := (hint sstar hsstar θ).1
      have hpos : 0 < tau * M.sys.ν θ * sstar θ :=
        mul_pos (mul_pos htau (hM.nu_pos θ)) hs0
      have hz : s θ / sstar θ - 1 - Real.log (s θ / sstar θ) = 0 := by
        rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hpos.ne'
        · exact h'
      by_contra hne
      have hr1 : s θ / sstar θ ≠ 1 := by
        intro h1
        apply hne
        field_simp at h1
        linarith
      have := Real.log_lt_sub_one_of_pos (div_pos (hspos θ) hs0) hr1
      linarith
    rw [heq]
    exact hsstar
  · intro hst
    refine ⟨fun θ => ⟨(hint s hst θ).1, (hint s hst θ).2.le⟩, ?_⟩
    intro s' hs'
    have hL := hlow s hst s' (fun θ => (hs' θ).1)
    have hN := Finset.sum_nonneg (fun θ (_ : θ ∈ (Finset.univ : Finset Θ)) =>
      hnn s hst s' (fun θ => (hs' θ).1) θ)
    linarith

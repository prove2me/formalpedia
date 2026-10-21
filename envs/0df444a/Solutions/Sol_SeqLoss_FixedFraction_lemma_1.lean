-- Prove2me | solution 1 for SeqLoss.FixedFraction.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:36:06.57303+00:00
-- url     : https://prove2.me/submissions/ea93806f-fdd8-456e-a7b7-d91b08b99966

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_FixedFraction_Axioms

set_option autoImplicit false
open SeqLoss.FixedFraction

theorem solution (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ)
    (hadd : Additive φ) (n : ℕ) (ℓ : Fin n → ℝ) (hℓ : IsLoss ℓ) (α : ℝ) (hα : 0 ≤ α) :
    φ n (α • ℓ) = α • φ n ℓ := by
  have hsm : ∀ (c : ℝ) (m : Fin n → ℝ), 0 ≤ c → IsLoss m → IsLoss (c • m) := by
    intro c m hc hm i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg hc (hm i)
  have hz : IsLoss (0 : Fin n → ℝ) := fun i => le_rfl
  have h0 : φ n 0 = 0 := by
    have := hadd n 0 0 hz hz
    simpa using this
  have hnat : ∀ m : ℕ, ∀ ℓ' : Fin n → ℝ, IsLoss ℓ' → φ n ((m : ℝ) • ℓ') = (m : ℝ) • φ n ℓ' := by
    intro m ℓ' hℓ'
    induction m with
    | zero => simp [h0]
    | succ m ih =>
      push_cast
      rw [add_smul, one_smul, hadd n _ _ (hsm _ _ (Nat.cast_nonneg m) hℓ') hℓ', ih, add_smul, one_smul]
  have hrat : ∀ p q : ℕ, 0 < q → φ n (((p : ℝ) / q) • ℓ) = ((p : ℝ) / q) • φ n ℓ := by
    intro p q hq
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have h1 := hnat q (((p : ℝ) / q) • ℓ) (hsm _ _ (by positivity) hℓ)
    have e : (q : ℝ) • (((p : ℝ) / q) • ℓ) = (p : ℝ) • ℓ := by
      rw [smul_smul]; congr 1; field_simp
    rw [e, hnat p ℓ hℓ] at h1
    apply smul_right_injective (Fin n → ℝ) hq0
    simp only []
    rw [← h1, smul_smul]
    congr 1
    field_simp
  rcases hα.eq_or_lt with h | hαpos
  · subst h; simp [h0]
  have hl' : IsLoss (α • ℓ) := hsm _ _ hα hℓ
  -- rational approximations
  set r : ℕ → ℝ := fun k => (⌊α * ((k : ℝ) + 1)⌋₊ : ℝ) / ((k : ℝ) + 1) with hr
  have hk : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  have hr_le : ∀ k : ℕ, r k ≤ α := by
    intro k
    rw [hr]; simp only []
    rw [div_le_iff₀ (hk k)]
    exact Nat.floor_le (by positivity)
  have hr_ge : ∀ k : ℕ, α - 1 / ((k : ℝ) + 1) ≤ r k := by
    intro k
    rw [hr]; simp only []
    have h := Nat.lt_floor_add_one (α * ((k : ℝ) + 1))
    rw [le_div_iff₀ (hk k), sub_mul, one_div, inv_mul_cancel₀ (hk k).ne']
    linarith
  have hr_tend : Filter.Tendsto r Filter.atTop (nhds α) := by
    have hup : Filter.Tendsto (fun k : ℕ => α - 1 / ((k : ℝ) + 1)) Filter.atTop (nhds (α - 0)) :=
      tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
    rw [sub_zero] at hup
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hup tendsto_const_nhds hr_ge hr_le
  have ha_tend : Filter.Tendsto (fun k => r k / α) Filter.atTop (nhds 1) := by
    have := hr_tend.div_const α
    rwa [div_self hαpos.ne'] at this
  have hcont := (hφ n (α • ℓ) hl').2
  have hlim1 : Filter.Tendsto (fun k => φ n ((r k / α) • (α • ℓ))) Filter.atTop (nhds (φ n (α • ℓ))) :=
    hcont.comp ha_tend
  have hlim2 : Filter.Tendsto (fun k => φ n ((r k / α) • (α • ℓ))) Filter.atTop (nhds (α • φ n ℓ)) := by
    have : ∀ k, φ n ((r k / α) • (α • ℓ)) = r k • φ n ℓ := by
      intro k
      have e : (r k / α) • (α • ℓ) = (((⌊α * ((k : ℝ) + 1)⌋₊ : ℕ) : ℝ) / (((k + 1 : ℕ)) : ℝ)) • ℓ := by
        rw [smul_smul, div_mul_cancel₀ _ hαpos.ne']
        simp only [hr]
        push_cast
        rfl
      rw [e, hrat _ (k + 1) (by omega)]
      simp only [hr]
      push_cast
      rfl
    simp_rw [this]
    exact hr_tend.smul_const _
  exact tendsto_nhds_unique hlim1 hlim2

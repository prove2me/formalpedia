-- Prove2me | solution 1 for SpecActions.thm4_cost_limit
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-12T04:26:58.946691+00:00
-- url     : https://prove2.me/submissions/11543b08-2f98-46b2-9076-c55c9b4a9326

import Mathlib
import Definitions.Def_SpecActions_model

open Finset SpecActions Filter Topology

private theorem hits_eq_closed (p : ℝ) (hp : 1 + p ≠ 0) (n : ℕ) :
    hits p n = hitsClosed p n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [hits, hitsClosed]
    | 1 =>
      simp only [hits, hitsClosed, Nat.cast_one, pow_one]
      field_simp
      ring
    | (k + 2) =>
      rw [hits, ih k (by omega), ih (k + 1) (by omega)]
      unfold hitsClosed
      have h1 : (-p) ^ (k + 1) = -p * (-p) ^ k := by ring
      have h2 : (-p) ^ (k + 2) = p ^ 2 * (-p) ^ k := by ring
      rw [h1, h2]
      push_cast
      field_simp
      ring

/-- The normalized hit counter converges to `p/(1+p)`. -/
private theorem tendsto_avg (pk : ℝ) (hpk0 : 0 ≤ pk) (hpk1 : pk ≤ 1) :
    Tendsto (fun T : ℕ =>
        pk / (1 + pk) * (1 - 1 / (T : ℝ))
          + pk ^ 2 / (1 + pk) ^ 2 * (1 - (-pk) ^ (T - 1)) / (T : ℝ))
      atTop (𝓝 (pk / (1 + pk))) := by
  have hz : Tendsto (fun T : ℕ => (1 : ℝ) / (T : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h1 : Tendsto (fun T : ℕ => pk / (1 + pk) * (1 - 1 / (T : ℝ))) atTop
      (𝓝 (pk / (1 + pk) * (1 - 0))) := (tendsto_const_nhds.sub hz).const_mul _
  have hg : Tendsto (fun T : ℕ => (2 * |pk ^ 2 / (1 + pk) ^ 2|) * (1 / (T : ℝ)))
      atTop (𝓝 0) := by
    simpa using hz.const_mul (2 * |pk ^ 2 / (1 + pk) ^ 2|)
  have hbound : ∀ T : ℕ,
      ‖pk ^ 2 / (1 + pk) ^ 2 * (1 - (-pk) ^ (T - 1)) / (T : ℝ)‖
        ≤ (2 * |pk ^ 2 / (1 + pk) ^ 2|) * (1 / (T : ℝ)) := by
    intro T
    rcases Nat.eq_zero_or_pos T with h | h
    · subst h; simp
    · have hT : (0 : ℝ) < (T : ℝ) := by exact_mod_cast h
      have habs : |(-pk) ^ (T - 1)| ≤ 1 := by
        rw [abs_pow, abs_neg, abs_of_nonneg hpk0]
        exact pow_le_one₀ hpk0 hpk1
      have hnum : |1 - (-pk) ^ (T - 1)| ≤ 2 := by
        rw [abs_le] at habs ⊢
        constructor <;> linarith [habs.1, habs.2]
      have heq : ‖pk ^ 2 / (1 + pk) ^ 2 * (1 - (-pk) ^ (T - 1)) / (T : ℝ)‖
          = |pk ^ 2 / (1 + pk) ^ 2| * |1 - (-pk) ^ (T - 1)| / (T : ℝ) := by
        rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hT]
      rw [heq]
      have hstep : |pk ^ 2 / (1 + pk) ^ 2| * |1 - (-pk) ^ (T - 1)| / (T : ℝ)
          ≤ |pk ^ 2 / (1 + pk) ^ 2| * 2 / (T : ℝ) := by
        gcongr
      calc |pk ^ 2 / (1 + pk) ^ 2| * |1 - (-pk) ^ (T - 1)| / (T : ℝ)
          ≤ |pk ^ 2 / (1 + pk) ^ 2| * 2 / (T : ℝ) := hstep
        _ = (2 * |pk ^ 2 / (1 + pk) ^ 2|) * (1 / (T : ℝ)) := by ring
  have h2 : Tendsto (fun T : ℕ =>
      pk ^ 2 / (1 + pk) ^ 2 * (1 - (-pk) ^ (T - 1)) / (T : ℝ)) atTop (𝓝 0) :=
    squeeze_zero_norm hbound hg
  have := h1.add h2
  simpa using this

private theorem thm4_cost_finite_horizon (T : ℕ) (α β pk kt : ℝ) (hT : 1 ≤ T)
    (hα : 0 < α) (hβ : 0 < β) (hpk0 : 0 ≤ pk) (hpk1 : pk ≤ 1) :
    (specCost T α β pk kt - seqCost T β) / seqCost T β
      = kt - (1 / (T : ℝ)) * (kt + α / (α + β)) *
          (((T : ℝ) - 1) * pk / (1 + pk)
            + pk ^ 2 / (1 + pk) ^ 2
            - pk ^ 2 / (1 + pk) ^ 2 * (-pk) ^ (T - 1)) := by
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hT
  have hpkne : (1 : ℝ) + pk ≠ 0 := by positivity
  have hab : α + β ≠ 0 := by positivity
  have hcast : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
    rw [Nat.cast_sub hT, Nat.cast_one]
  unfold specCost seqCost
  rw [hits_eq_closed pk hpkne]
  unfold hitsClosed
  rw [hcast]
  field_simp
  ring

theorem solution (α β pk kt : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hpk0 : 0 ≤ pk) (hpk1 : pk ≤ 1) :
    Tendsto (fun T : ℕ => (specCost T α β pk kt - seqCost T β) / seqCost T β)
      atTop (𝓝 (kt - (kt + α / (α + β)) * (pk / (1 + pk)))) := by
  have hpkne : (1 : ℝ) + pk ≠ 0 := by positivity
  have hab : α + β ≠ 0 := by positivity
  have key : ∀ T : ℕ, 1 ≤ T →
      (kt - (kt + α / (α + β)) *
          (pk / (1 + pk) * (1 - 1 / (T : ℝ))
            + pk ^ 2 / (1 + pk) ^ 2 * (1 - (-pk) ^ (T - 1)) / (T : ℝ)))
        = (specCost T α β pk kt - seqCost T β) / seqCost T β := by
    intro T hT
    have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hT
    rw [thm4_cost_finite_horizon T α β pk kt hT hα hβ hpk0 hpk1]
    field_simp
    ring
  have hlim := (tendsto_avg pk hpk0 hpk1).const_mul (kt + α / (α + β))
  have hlim2 : Tendsto (fun T : ℕ =>
      kt - (kt + α / (α + β)) *
        (pk / (1 + pk) * (1 - 1 / (T : ℝ))
          + pk ^ 2 / (1 + pk) ^ 2 * (1 - (-pk) ^ (T - 1)) / (T : ℝ)))
      atTop (𝓝 (kt - (kt + α / (α + β)) * (pk / (1 + pk)))) := tendsto_const_nhds.sub hlim
  exact hlim2.congr' (Filter.eventually_atTop.2 ⟨1, key⟩)


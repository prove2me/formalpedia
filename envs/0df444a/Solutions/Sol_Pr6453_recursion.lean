-- Prove2me | solution 1 for Pr6453.recursion
-- status  : ACCEPTED   (prove)
-- author  : @gustasmickus
-- created : 2026-11-08T16:24:57.061502+00:00
-- url     : https://prove2.me/submissions/024c093f-7ea7-4061-b1a7-9784cf7782cc

/-
PR #6453: the recursion composing the per-call invoices into the running time.
-/
import Definitions.Def_Pr6453_RankMoments
import Definitions.Def_Pr6453_Recursion
import Definitions.Def_IntMul_MultitapeModel
import Theorems.Thm_Pr6453_moment_kappa_gt

set_option autoImplicit false

namespace Pr6453

noncomputable section

open Finset

/-! ## Positivity of the two moments -/

theorem moment_targets_pos (τ : ℝ) : 0 < moment targets τ := by
  simp only [moment, targets, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  positivity

theorem moment_paid_pos (τ : ℝ) : 0 < moment paid τ := by
  simp only [moment, paid, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  positivity

/-! ## The contraction ratio -/


theorem gamma_nonneg : 0 ≤ gamma := by
  rw [gamma]
  exact div_nonneg (le_of_lt (moment_paid_pos _)) (le_of_lt (moment_targets_pos _))

/-- **The price inequality is exactly `gamma < 1`.** -/
theorem gamma_lt_one : gamma < 1 := by
  rw [gamma, div_lt_one (moment_targets_pos _)]
  exact moment_kappa_gt

/-! ## The geometric composition -/

/-- The finite geometric sum is bounded by `1/(1-γ)`. -/
theorem geom_sum_le_one_div {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ < 1) (n : ℕ) :
    (∑ i ∈ Finset.range n, γ ^ i) ≤ 1 / (1 - γ) := by
  have hpos : (0 : ℝ) < 1 - γ := by linarith
  rw [geom_sum_eq (by linarith : γ ≠ 1)]
  have h2 : (γ ^ n - 1) / (γ - 1) = (1 - γ ^ n) / (1 - γ) := by
    rw [div_eq_div_iff (by linarith) (ne_of_gt hpos)]
    ring
  rw [h2, div_le_div_iff_of_pos_right hpos]
  have : (0 : ℝ) ≤ γ ^ n := pow_nonneg h0 n
  linarith

/-- **The recursion.** If every level of the call tree costs at most the fraction `gamma` of the
level above it, the whole tree costs at most `1/(1-gamma)` times its root, whatever the depth. -/
theorem recursion_bound (C : ℕ → ℝ) (h0 : 0 ≤ C 0) (hstep : ∀ j, C (j + 1) ≤ gamma * C j) :
    ∀ L : ℕ, (∑ j ∈ Finset.range L, C j) ≤ C 0 / (1 - gamma) := by
  intro L
  have hC : ∀ j : ℕ, C j ≤ gamma ^ j * C 0 := by
    intro j
    induction j with
    | zero => simp
    | succ k ih =>
        calc C (k + 1) ≤ gamma * C k := hstep k
          _ ≤ gamma * (gamma ^ k * C 0) :=
              mul_le_mul_of_nonneg_left ih gamma_nonneg
          _ = gamma ^ (k + 1) * C 0 := by ring
  have hsum : (∑ j ∈ Finset.range L, C j) ≤ (∑ j ∈ Finset.range L, gamma ^ j) * C 0 := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => hC j
  have hgeom : (∑ j ∈ Finset.range L, gamma ^ j) ≤ 1 / (1 - gamma) :=
    geom_sum_le_one_div gamma_nonneg gamma_lt_one L
  have hlt : gamma < 1 := gamma_lt_one
  have h1gamma : (0 : ℝ) < 1 - gamma := by linarith
  calc (∑ j ∈ Finset.range L, C j) ≤ (∑ j ∈ Finset.range L, gamma ^ j) * C 0 := hsum
    _ ≤ (1 / (1 - gamma)) * C 0 := by
        exact mul_le_mul_of_nonneg_right hgeom h0
    _ = C 0 / (1 - gamma) := by ring

/-- **The recursion, in the campaign's terms.** A root cost of `c·n·(lg n)^(1-κ)` and a per-level
contraction by `gamma` give a total cost of `(c/(1-gamma))·n·(lg n)^(1-κ)`: the exponent survives
the recursion. -/
theorem recursion_bound_kappa (C : ℕ → ℝ) (c : ℝ) (n L : ℕ) (hc : 0 ≤ c)
    (hC0 : 0 ≤ C 0)
    (hroot : C 0 ≤ c * (n : ℝ) * ((IntMul.lg n : ℝ) ^ (1 - (kappa : ℝ))))
    (hstep : ∀ j, C (j + 1) ≤ gamma * C j) :
    (∑ j ∈ Finset.range L, C j) ≤
      (c / (1 - gamma)) * (n : ℝ) * ((IntMul.lg n : ℝ) ^ (1 - (kappa : ℝ))) := by
  have hlg : (0 : ℝ) < (IntMul.lg n : ℝ) := by
    have : 0 < IntMul.lg n := Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
    exact_mod_cast this
  have h0 : 0 ≤ C 0 := hC0
  have hlt : gamma < 1 := gamma_lt_one
  have h1gamma : (0 : ℝ) < 1 - gamma := by linarith
  calc (∑ j ∈ Finset.range L, C j) ≤ C 0 / (1 - gamma) := recursion_bound C h0 hstep L
    _ ≤ (c * (n : ℝ) * ((IntMul.lg n : ℝ) ^ (1 - (kappa : ℝ)))) / (1 - gamma) := by
        exact div_le_div_of_nonneg_right hroot (le_of_lt h1gamma)
    _ = (c / (1 - gamma)) * (n : ℝ) * ((IntMul.lg n : ℝ) ^ (1 - (kappa : ℝ))) := by ring

/-- **The composition, gathered.** The invoice's price inequality makes the contraction ratio
strictly below one, and then the whole call tree costs at most a constant multiple of its root,
with the same exponent `1-κ` on the logarithm. -/
theorem recursion :
    gamma < 1 ∧
      (∀ (C : ℕ → ℝ), 0 ≤ C 0 → (∀ j, C (j + 1) ≤ gamma * C j) →
        ∀ L : ℕ, (∑ j ∈ Finset.range L, C j) ≤ C 0 / (1 - gamma)) ∧
      (∀ (C : ℕ → ℝ) (c : ℝ) (n L : ℕ), 0 ≤ c → 0 ≤ C 0 →
        C 0 ≤ c * (n : ℝ) * ((IntMul.lg n : ℝ) ^ (1 - (kappa : ℝ))) →
        (∀ j, C (j + 1) ≤ gamma * C j) →
        (∑ j ∈ Finset.range L, C j) ≤
          (c / (1 - gamma)) * (n : ℝ) * ((IntMul.lg n : ℝ) ^ (1 - (kappa : ℝ)))) :=
  ⟨gamma_lt_one, fun C h0 hstep L => recursion_bound C h0 hstep L,
    fun C c n L hc h0 hroot hstep => recursion_bound_kappa C c n L hc h0 hroot hstep⟩

end
end Pr6453

/-- **The recursion of PR #6453.** -/
theorem solution :
    Pr6453.gamma < 1 ∧
      (∀ (C : ℕ → ℝ), 0 ≤ C 0 → (∀ j, C (j + 1) ≤ Pr6453.gamma * C j) →
        ∀ L : ℕ, (∑ j ∈ Finset.range L, C j) ≤ C 0 / (1 - Pr6453.gamma)) ∧
      (∀ (C : ℕ → ℝ) (c : ℝ) (n L : ℕ), 0 ≤ c → 0 ≤ C 0 →
        C 0 ≤ c * (n : ℝ) * ((IntMul.lg n : ℝ) ^ (1 - (Pr6453.kappa : ℝ))) →
        (∀ j, C (j + 1) ≤ Pr6453.gamma * C j) →
        (∑ j ∈ Finset.range L, C j) ≤
          (c / (1 - Pr6453.gamma)) * (n : ℝ) *
            ((IntMul.lg n : ℝ) ^ (1 - (Pr6453.kappa : ℝ)))) :=
  Pr6453.recursion

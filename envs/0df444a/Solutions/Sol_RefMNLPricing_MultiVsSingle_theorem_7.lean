-- Prove2me | solution 1 for RefMNLPricing.MultiVsSingle.theorem_7
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T06:03:45.173992+00:00
-- url     : https://prove2.me/submissions/920adbd6-6bc7-4fb6-a997-5508308fc3ff

import Mathlib
import Definitions.Def_RefMNLPricing_MultiVsSingle_Model

/-! Counterexample to `RefMNLPricing.MultiVsSingle.theorem_7`, part 2.

`n = 3`, `a = 2/5`, `b = 1/10`, `c = 9/10` (so `b + c = 1`), `α = 0`, `β = 9/10`, `p_H = 4`.
The myopic steady state is `p^{m⋆} = 4 = Π^{m⋆} + 1`, `Π^{m⋆} = 3`, and it solves the ceiling
equation (9), so `p_H = p̂_H` satisfies the ceiling assumption. Conditions (26a), (26b) and
`αb + c > 0` hold. But every single-period revenue on the box is at most `3 = Π(4·1, 4·1)`,
so the constant price `x = 4·1` is an optimal steady state, contradicting part 2. -/

namespace Cex45706e42

open RefMNLPricing

/-- One-product key bound: `(p - 3) e^{u} ≤ 1` when `u ≤ 4 - p`. -/
theorem term_le {p r : ℝ} (hr : r ≤ 4) :
    (p - 3) * Real.exp (2 / 5 - 1 / 10 * p + 9 / 10 * max (r - p) 0 - 9 / 10 * max (p - r) 0)
      ≤ 1 := by
  have h1 : max (r - p) 0 - max (p - r) 0 = r - p := by
    rcases le_total r p with h | h
    · rw [max_eq_right (by linarith : r - p ≤ 0), max_eq_left (by linarith : 0 ≤ p - r)]; ring
    · rw [max_eq_left (by linarith : 0 ≤ r - p), max_eq_right (by linarith : p - r ≤ 0)]; ring
  have hu4 : 2 / 5 - 1 / 10 * p + 9 / 10 * max (r - p) 0 - 9 / 10 * max (p - r) 0 ≤ 4 - p := by
    linarith
  rcases le_or_gt (p - 3) 0 with h | h
  · nlinarith [Real.exp_pos (2 / 5 - 1 / 10 * p + 9 / 10 * max (r - p) 0 - 9 / 10 * max (p - r) 0)]
  · have hle := Real.exp_le_exp.mpr hu4
    have hlow : (p - 4) + 1 ≤ Real.exp (p - 4) := Real.add_one_le_exp _
    have hprod : Real.exp (p - 4) * Real.exp (4 - p) = 1 := by
      rw [← Real.exp_add]; simp
    calc _ ≤ (p - 3) * Real.exp (4 - p) := mul_le_mul_of_nonneg_left hle h.le
      _ ≤ Real.exp (p - 4) * Real.exp (4 - p) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = 1 := hprod

theorem alg (p0 p1 p2 E0 E1 E2 : ℝ) (he0 : 0 < E0) (he1 : 0 < E1) (he2 : 0 < E2)
    (h0 : (p0 - 3) * E0 ≤ 1) (h1 : (p1 - 3) * E1 ≤ 1) (h2 : (p2 - 3) * E2 ≤ 1) :
    p0 * (E0 / (1 + (E0 + E1 + E2))) + p1 * (E1 / (1 + (E0 + E1 + E2))) +
      p2 * (E2 / (1 + (E0 + E1 + E2))) ≤ 3 := by
  have hD : 0 < 1 + (E0 + E1 + E2) := by linarith
  rw [mul_div_assoc', mul_div_assoc', mul_div_assoc', ← add_div, ← add_div, div_le_iff₀ hD]
  nlinarith

theorem revenue_le (p r : Fin 3 → ℝ) (hr : ∀ i, r i ≤ 4) :
    Myopic.revenue (fun _ : Fin 3 => (2 / 5 : ℝ)) (fun _ => 1 / 10) (fun _ => 9 / 10)
      (fun _ => 9 / 10) p r ≤ 3 := by
  simp only [Myopic.revenue, Myopic.share, Myopic.util, Fin.sum_univ_three]
  exact alg _ _ _ _ _ _ (Real.exp_pos _) (Real.exp_pos _) (Real.exp_pos _)
    (term_le (hr 0)) (term_le (hr 1)) (term_le (hr 2))

theorem revenue_nonneg (p r : Fin 3 → ℝ) (hp : ∀ i, 0 ≤ p i) :
    0 ≤ Myopic.revenue (fun _ : Fin 3 => (2 / 5 : ℝ)) (fun _ => 1 / 10) (fun _ => 9 / 10)
      (fun _ => 9 / 10) p r := by
  unfold Myopic.revenue
  refine Finset.sum_nonneg fun i _ => mul_nonneg (hp i) ?_
  unfold Myopic.share
  positivity

theorem refPath_le (p : ℕ → Fin 3 → ℝ) (hp : ∀ t i, p t i ≤ 4) (t : ℕ) (i : Fin 3) :
    Gap.refPath 0 (fun _ => (4 : ℝ)) p t i ≤ 4 := by
  cases t with
  | zero => simp [Gap.refPath]
  | succ t => simpa [Gap.refPath] using hp t i

theorem revenue_x :
    Myopic.revenue (fun _ : Fin 3 => (2 / 5 : ℝ)) (fun _ => 1 / 10) (fun _ => 9 / 10)
      (fun _ => 9 / 10) (fun _ => 4) (fun _ => 4) = 3 := by
  simp only [Myopic.revenue, Myopic.share, Myopic.util, Fin.sum_univ_three]
  norm_num

theorem disc_le (P : ℕ → Fin 3 → Set.Icc (0 : ℝ) 4) :
    Gap.disc (fun _ : Fin 3 => (2 / 5 : ℝ)) (fun _ => 1 / 10) (fun _ => 9 / 10) (fun _ => 9 / 10)
      0 (9 / 10) (fun t i => (P t i : ℝ)) (fun _ => 4) ≤ 30 := by
  unfold Gap.disc
  set p : ℕ → Fin 3 → ℝ := fun t i => (P t i : ℝ) with hpdef
  have hp0 : ∀ t i, 0 ≤ p t i := fun t i => (P t i).2.1
  have hp4 : ∀ t i, p t i ≤ 4 := fun t i => (P t i).2.2
  have hg : Summable (fun t : ℕ => (9 / 10 : ℝ) ^ t * 3) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  have hle : ∀ t : ℕ, (9 / 10 : ℝ) ^ t *
      Myopic.revenue (fun _ : Fin 3 => (2 / 5 : ℝ)) (fun _ => 1 / 10) (fun _ => 9 / 10)
        (fun _ => 9 / 10) (p t) (Gap.refPath 0 (fun _ => 4) p t) ≤ (9 / 10 : ℝ) ^ t * 3 :=
    fun t => mul_le_mul_of_nonneg_left (revenue_le _ _ (refPath_le p hp4 t)) (by positivity)
  have hnn : ∀ t : ℕ, 0 ≤ (9 / 10 : ℝ) ^ t *
      Myopic.revenue (fun _ : Fin 3 => (2 / 5 : ℝ)) (fun _ => 1 / 10) (fun _ => 9 / 10)
        (fun _ => 9 / 10) (p t) (Gap.refPath 0 (fun _ => 4) p t) :=
    fun t => mul_nonneg (by positivity) (revenue_nonneg _ _ (hp0 t))
  have hf := Summable.of_nonneg_of_le hnn hle hg
  calc _ ≤ ∑' t : ℕ, (9 / 10 : ℝ) ^ t * 3 := Summable.tsum_le_tsum hle hf hg
    _ = 30 := by
      rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num

theorem opt_steady :
    GainSeeking.IsOptSteadyState (fun _ : Fin 3 => (2 / 5 : ℝ)) (fun _ => 1 / 10)
      (fun _ => 9 / 10) (fun _ => 9 / 10) 0 (9 / 10) 4 (fun _ => 4) := by
  refine ⟨fun _ => ⟨by norm_num, le_refl _⟩, ?_⟩
  rw [revenue_x]
  have hne : Nonempty (ℕ → Fin 3 → Set.Icc (0 : ℝ) 4) :=
    ⟨fun _ _ => ⟨4, by norm_num, le_refl _⟩⟩
  unfold GainSeeking.optValue
  refine (ciSup_le fun P => disc_le P).trans ?_
  norm_num

theorem ceiling :
    Gap.CeilingOK (fun _ : Fin 3 => (2 / 5 : ℝ)) (fun _ => 1 / 10) (fun _ => 9 / 10)
      (fun _ => 9 / 10) 4 := by
  refine ⟨4, ?_, le_refl _⟩
  have hchi : Myopic.chi (fun _ : Fin 3 => (2 / 5 : ℝ)) (fun _ => 1 / 10) (fun _ => 9 / 10)
      (fun _ => 9 / 10) = 1 := by
    simp [Myopic.chi]
    norm_num
  rw [Myopic.ceilRHS, hchi]
  simp only [Fin.sum_univ_three]
  norm_num

theorem zeta_prod :
    MultiVsSingle.zeta1 3 (2 / 5) (9 / 10) (3 + 1 / (1 / 10 + 9 / 10)) *
      Real.exp (-(1 / 10 + 9 / 10) * 4) = 3 := by
  unfold MultiVsSingle.zeta1
  rw [← Real.exp_add]
  rw [show (2 / 5 : ℝ) + Real.log ((3 : ℕ) : ℝ) + 9 / 10 * (3 + 1 / (1 / 10 + 9 / 10)) +
      -(1 / 10 + 9 / 10) * 4 = Real.log 3 by push_cast; ring]
  exact Real.exp_log (by norm_num)

end Cex45706e42

open RefMNLPricing.MultiVsSingle in
theorem solution : ¬ (∀ {n : ℕ} (a b c α β pH : ℝ)
    (hn : 2 ≤ n) (hb : 0 < b) (hc : 0 ≤ c)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Ico (0 : ℝ) 1) (hpH : 0 < pH)
    (hceil : RefMNLPricing.Gap.CeilingOK (fun _ : Fin n => a) (fun _ => b) (fun _ => c) (fun _ => c) pH),
    ((¬ ∃ y, IsSingleSteadyState (fun _ : Fin n => a) (fun _ => b) (fun _ => c) (fun _ => c)
          α β pH y) →
      ∀ x : Fin n → ℝ,
        ¬ RefMNLPricing.GainSeeking.IsOptSteadyState (fun _ => a) (fun _ => b) (fun _ => c) (fun _ => c) α β pH x) ∧
    (∀ Rms : ℝ, Rms = n / (b + c) * Real.exp (a - b * Rms - b / (b + c)) →
      0 < α * b + c →
      pH * (1 - zeta1 n a c (Rms + 1 / (b + c)) * Real.exp (-(b + c) * pH))
          - zeta1 n a c (Rms + 1 / (b + c)) * zeta2 α b c * Real.exp (-(b + c) * pH)
          ≤ zeta2 α b c →
      ((1 - RefMNLPricing.SteadyState.kappa α β) ^ 2 + β * (1 - α * RefMNLPricing.SteadyState.kappa α β) ^ 2) * c ^ 2
          - (1 + β * α ^ 2) * (b + c * RefMNLPricing.SteadyState.kappa α β) ^ 2 ≥
          ((b + c) ^ 2 + β * (α * b + c) ^ 2) / ((n : ℝ) - 1) →
      (∃ y, IsSingleSteadyState (fun _ : Fin n => a) (fun _ => b) (fun _ => c) (fun _ => c)
          α β pH y) ∧
      ∀ x : Fin n → ℝ,
        ¬ RefMNLPricing.GainSeeking.IsOptSteadyState (fun _ => a) (fun _ => b) (fun _ => c) (fun _ => c) α β pH x)) := by
  intro h
  have h2 := (h (n := 3) (2 / 5) (1 / 10) (9 / 10) 0 (9 / 10) 4 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) Cex45706e42.ceiling).2 3
  have hz2 : zeta2 0 (1 / 10) (9 / 10) = 1 := by norm_num [zeta2]
  refine ((h2 ?_ ?_ ?_ ?_).2 (fun _ => 4)) Cex45706e42.opt_steady
  · norm_num
  · norm_num
  · rw [hz2, mul_one, Cex45706e42.zeta_prod]
    norm_num
  · norm_num [RefMNLPricing.SteadyState.kappa]

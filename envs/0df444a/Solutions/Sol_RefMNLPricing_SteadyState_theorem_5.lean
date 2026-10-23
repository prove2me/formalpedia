-- Prove2me | solution 1 for RefMNLPricing.SteadyState.theorem_5
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T22:44:01.168225+00:00
-- url     : https://prove2.me/submissions/cf5a62f5-ba82-4088-9de5-2b019fc642c6

import Mathlib
import Definitions.Def_RefMNLPricing_SteadyState_Model

/-! Counterexample to `RefMNLPricing.SteadyState.theorem_5`.

One product, `a = b = c⁺ = c⁻ = 1`, `α = 0`, `β = 1/2`, `p_H = 1`. The ceiling equation (9) has
the solution `p̂_H = 1 = p_H`, so the ceiling assumption holds. Every single-period revenue on the
box is at most `1/2 = Π(1, 1)`, so the constant price `x = 1` is an optimal steady state. But
`x - Π(x, x) = 1/2`, while the interval of (20) is `[2/3, 2/3]` (`κ = 1/2`). -/

namespace Cex36d48a78

open RefMNLPricing

/-- The logistic factor is monotone. -/
theorem logistic_mono {u v : ℝ} (h : u ≤ v) :
    Real.exp u / (1 + Real.exp u) ≤ Real.exp v / (1 + Real.exp v) := by
  have hu := Real.exp_pos u
  have hv := Real.exp_pos v
  have huv : Real.exp u ≤ Real.exp v := Real.exp_le_exp.mpr h
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- The key one-dimensional bound: `p · σ(u) ≤ 1/2` when `u ≤ 2 - 2p`, `0 ≤ p`. -/
theorem key_bound {p u : ℝ} (hp : 0 ≤ p) (hu : u ≤ 2 - 2 * p) :
    p * (Real.exp u / (1 + Real.exp u)) ≤ 1 / 2 := by
  have he := Real.exp_pos u
  have hle : Real.exp u ≤ Real.exp (2 - 2 * p) := Real.exp_le_exp.mpr hu
  have hlow : (2 * p - 2) + 1 ≤ Real.exp (2 * p - 2) := Real.add_one_le_exp _
  have hprod : Real.exp (2 * p - 2) * Real.exp (2 - 2 * p) = 1 := by
    rw [← Real.exp_add]; simp
  have hkey : (2 * p - 1) * Real.exp u ≤ 1 := by
    rcases le_or_gt (2 * p - 1) 0 with h | h
    · nlinarith
    · calc (2 * p - 1) * Real.exp u ≤ (2 * p - 1) * Real.exp (2 - 2 * p) :=
            mul_le_mul_of_nonneg_left hle h.le
        _ ≤ Real.exp (2 * p - 2) * Real.exp (2 - 2 * p) :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
        _ = 1 := hprod
  rw [mul_div_assoc', div_le_iff₀ (by linarith)]
  nlinarith

/-- The parameters. -/
noncomputable def one1 : Fin 1 → ℝ := fun _ => 1

theorem revenue_eq (p r : Fin 1 → ℝ) :
    Myopic.revenue one1 one1 one1 one1 p r =
      p 0 * (Real.exp (Myopic.util one1 one1 one1 one1 p r 0) /
        (1 + Real.exp (Myopic.util one1 one1 one1 one1 p r 0))) := by
  simp [Myopic.revenue, Myopic.share, Fin.sum_univ_one]

theorem revenue_le (p r : Fin 1 → ℝ) (hp : Myopic.InBox 1 p) (hr : Myopic.InBox 1 r) :
    Myopic.revenue one1 one1 one1 one1 p r ≤ 1 / 2 := by
  rw [revenue_eq]
  have hp0 := hp 0
  have hr0 := hr 0
  simp only [Set.mem_Icc] at hp0 hr0
  apply key_bound hp0.1
  simp only [Myopic.util, one1, one_mul]
  have h1 : max (r 0 - p 0) 0 ≤ 1 - p 0 := max_le (by linarith) (by linarith)
  have h2 : 0 ≤ max (p 0 - r 0) 0 := le_max_right _ _
  linarith

theorem revenue_nonneg (p r : Fin 1 → ℝ) (hp : Myopic.InBox 1 p) :
    0 ≤ Myopic.revenue one1 one1 one1 one1 p r := by
  rw [revenue_eq]
  have hp0 := (hp 0).1
  have := Real.exp_pos (Myopic.util one1 one1 one1 one1 p r 0)
  positivity

theorem refPath_inBox (r₀ : Fin 1 → ℝ) (hr : Myopic.InBox 1 r₀) (p : ℕ → Fin 1 → ℝ)
    (hp : ∀ t, Myopic.InBox 1 (p t)) (t : ℕ) : Myopic.InBox 1 (Gap.refPath 0 r₀ p t) := by
  cases t with
  | zero => simpa [Gap.refPath] using hr
  | succ t =>
    intro i
    simpa [Gap.refPath] using hp t i

theorem x_inBox : Myopic.InBox 1 one1 := fun _ => by simp [one1]

theorem revenue_x : Myopic.revenue one1 one1 one1 one1 one1 one1 = 1 / 2 := by
  rw [revenue_eq]
  simp [Myopic.util, one1]
  norm_num

theorem disc_le (P : ℕ → Fin 1 → Set.Icc (0 : ℝ) 1) :
    Gap.disc one1 one1 one1 one1 0 (1 / 2) (fun t i => (P t i : ℝ)) one1 ≤ 1 := by
  unfold Gap.disc
  set p : ℕ → Fin 1 → ℝ := fun t i => (P t i : ℝ) with hpdef
  have hpb : ∀ t, Myopic.InBox 1 (p t) := fun t i => (P t i).2
  have hrb := refPath_inBox one1 x_inBox p hpb
  have hg : Summable (fun t : ℕ => (1 / 2 : ℝ) ^ t * (1 / 2)) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  have hle : ∀ t : ℕ, (1 / 2 : ℝ) ^ t *
      Myopic.revenue one1 one1 one1 one1 (p t) (Gap.refPath 0 one1 p t) ≤ (1 / 2 : ℝ) ^ t * (1 / 2) :=
    fun t => mul_le_mul_of_nonneg_left (revenue_le _ _ (hpb t) (hrb t)) (by positivity)
  have hnn : ∀ t : ℕ, 0 ≤ (1 / 2 : ℝ) ^ t *
      Myopic.revenue one1 one1 one1 one1 (p t) (Gap.refPath 0 one1 p t) :=
    fun t => mul_nonneg (by positivity) (revenue_nonneg _ _ (hpb t))
  have hf : Summable (fun t : ℕ => (1 / 2 : ℝ) ^ t *
      Myopic.revenue one1 one1 one1 one1 (p t) (Gap.refPath 0 one1 p t)) :=
    Summable.of_nonneg_of_le hnn hle hg
  calc ∑' t, (1 / 2 : ℝ) ^ t * Myopic.revenue one1 one1 one1 one1 (p t) (Gap.refPath 0 one1 p t)
      ≤ ∑' t : ℕ, (1 / 2 : ℝ) ^ t * (1 / 2) := Summable.tsum_le_tsum hle hf hg
    _ = 1 := by
      rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num

theorem opt_steady : GainSeeking.IsOptSteadyState one1 one1 one1 one1 0 (1 / 2) 1 one1 := by
  refine ⟨x_inBox, ?_⟩
  rw [revenue_x]
  have hne : Nonempty (ℕ → Fin 1 → Set.Icc (0 : ℝ) 1) :=
    ⟨fun _ _ => ⟨1, by norm_num, le_refl _⟩⟩
  unfold GainSeeking.optValue
  refine (ciSup_le fun P => disc_le P).trans ?_
  norm_num

theorem ceiling : Gap.CeilingOK one1 one1 one1 one1 1 := by
  refine ⟨1, ?_, le_refl _⟩
  have hchi : Myopic.chi one1 one1 one1 one1 = 1 / 2 := by
    simp [Myopic.chi, one1]
    norm_num
  rw [Myopic.ceilRHS, hchi]
  simp [one1]
  norm_num

end Cex36d48a78

open RefMNLPricing.SteadyState in
theorem solution : ¬ (∀ {n : ℕ} (a b cp cm : Fin n → ℝ) (α β pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Ico (0 : ℝ) 1) (hpH : 0 < pH)
    (hceil : RefMNLPricing.Gap.CeilingOK a b cp cm pH)
    (hNoGain : ∀ i, cp i ≤ cm i)
    (x : Fin n → ℝ) (hx : RefMNLPricing.GainSeeking.IsOptSteadyState a b cp cm α β pH x),
    ∀ i, x i - RefMNLPricing.Myopic.revenue a b cp cm x x ∈
      Set.Icc (1 / (b i + cm i * kappa α β)) (1 / (b i + cp i * kappa α β))) := by
  intro h
  have hmem := h Cex36d48a78.one1 Cex36d48a78.one1 Cex36d48a78.one1 Cex36d48a78.one1 0 (1 / 2) 1
    (fun _ => by simp [Cex36d48a78.one1]) (fun _ => by simp [Cex36d48a78.one1])
    (fun _ => by simp [Cex36d48a78.one1]) (by norm_num) (by norm_num) (by norm_num)
    Cex36d48a78.ceiling (fun _ => le_refl _) Cex36d48a78.one1 Cex36d48a78.opt_steady 0
  rw [Cex36d48a78.revenue_x] at hmem
  have hk : kappa 0 (1 / 2) = 1 / 2 := by norm_num [kappa]
  rw [hk] at hmem
  have h1 := hmem.1
  simp [Cex36d48a78.one1] at h1
  norm_num at h1

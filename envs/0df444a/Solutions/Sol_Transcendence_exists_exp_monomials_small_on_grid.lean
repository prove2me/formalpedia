-- Prove2me | solution 1 for Transcendence.exists_exp_monomials_small_on_grid
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T09:17:18.670804+00:00
-- url     : https://prove2.me/submissions/87d34c0b-99c2-4d95-a394-f8feeaa04372

import Mathlib
import Theorems.Thm_Transcendence_siegel_small_values
import Theorems.Thm_Transcendence_polydisc_cauchy

/-!
# An auxiliary function that is small on the grid

Waldschmidt's §4.6, step 3 and (4.16). Node 3 (`siegel_small_values`) is applied to the exponential
monomials `φ_{τ,t}(z) = z_{k₀}^τ e^{⟨Σ tᵢxᵢ, z⟩}`, bounded by `R^T e^{cx T R}` on the polydisc of radius
`R = E r`, `r = (cy + 2) S₁`. The grid point `Σ s_j y_j` has norm at most `S₁ cy`, so the unit polydisc
around it lies in the polydisc of radius `r`, where `|F| ≤ e^{-U}`; Cauchy's inequality (node 0,
`polydisc_cauchy`) there gives (4.16). The same bound for the monomials gives the growth of `F`.
-/

namespace ExistsExpMonomialsSmallOnGrid

lemma prod_count_factorial_le {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} (L : Fin k → ι) :
    (∏ ν, ((Finset.univ.filter fun l => L l = ν).card.factorial : ℝ)) ≤ k.factorial := by
  have hsum : ∑ ν, (Finset.univ.filter fun l => L l = ν).card = k := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := L) (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
    simp
  have h := Nat.le_of_dvd (Nat.factorial_pos _) (Nat.prod_factorial_dvd_factorial_sum
    Finset.univ (fun ν => (Finset.univ.filter fun l => L l = ν).card))
  rw [hsum] at h
  exact_mod_cast h

lemma analyticAt_linear {ι : Type*} [Fintype ι] (c : ι → ℂ) (z : ι → ℂ) :
    AnalyticAt ℂ (fun z : ι → ℂ => ∑ ν, c ν * z ν) z := by
  have : (fun z : ι → ℂ => ∑ ν, c ν * z ν) = ∑ ν, fun z : ι → ℂ => c ν * z ν := by
    funext z; simp
  rw [this]
  exact Finset.analyticAt_sum _ fun ν _ =>
    analyticAt_const.mul ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) ν).analyticAt z)

lemma analytic_expMono {ι : Type*} [Fintype ι] (k₀ : ι) (τ : ℕ) (c : ι → ℂ) :
    AnalyticOnNhd ℂ (fun z : ι → ℂ => z k₀ ^ τ * Complex.exp (∑ ν, c ν * z ν)) Set.univ := by
  intro z _
  have h1 : AnalyticAt ℂ (fun z : ι → ℂ => z k₀) z :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) k₀).analyticAt z
  exact (h1.pow τ).mul (analyticAt_linear c z).cexp

/-- `|z_{k₀}^τ e^{⟨c, z⟩}| ≤ R^{τmax} e^{Cc R}` on the polydisc of radius `R ≥ 1`, if `Σ |c_ν| ≤ Cc`. -/
lemma norm_expMono_le {ι : Type*} [Fintype ι] (k₀ : ι) {τ τmax : ℕ} (hτ : τ ≤ τmax) (c : ι → ℂ)
    {R Cc : ℝ} (hR : 1 ≤ R) (hc : ∑ ν, ‖c ν‖ ≤ Cc) {z : ι → ℂ} (hz : ‖z‖ ≤ R) :
    ‖z k₀ ^ τ * Complex.exp (∑ ν, c ν * z ν)‖ ≤ R ^ τmax * Real.exp (Cc * R) := by
  have hzk : ‖z k₀‖ ≤ R := (norm_le_pi_norm z k₀).trans hz
  rw [norm_mul, norm_pow, Complex.norm_exp]
  apply mul_le_mul _ _ (Real.exp_pos _).le (by positivity)
  · calc ‖z k₀‖ ^ τ ≤ R ^ τ := pow_le_pow_left₀ (norm_nonneg _) hzk τ
      _ ≤ R ^ τmax := pow_le_pow_right₀ hR hτ
  · apply Real.exp_le_exp.mpr
    calc (∑ ν, c ν * z ν).re ≤ ‖∑ ν, c ν * z ν‖ := Complex.re_le_norm _
      _ ≤ ∑ ν, ‖c ν * z ν‖ := norm_sum_le _ _
      _ ≤ ∑ ν, ‖c ν‖ * R := by
          gcongr with ν
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm z ν).trans hz) (norm_nonneg _)
      _ = (∑ ν, ‖c ν‖) * R := by rw [Finset.sum_mul]
      _ ≤ Cc * R := mul_le_mul_of_nonneg_right hc (by linarith)

/-- The cardinality of the index set of the exponential monomials. -/
lemma card_Λ {d₀ d₁ T : ℕ} (hd₀ : d₀ ≤ 1) :
    Fintype.card (Fin (d₀ * T + 1) × (Fin d₁ → Fin (T + 1))) = (T + 1) ^ (d₀ + d₁) := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd₀ with rfl | rfl
  · simp
  · simp; ring

end ExistsExpMonomialsSmallOnGrid

open ExistsExpMonomialsSmallOnGrid Metric in
/-- **An auxiliary function that is small on the grid** (DALAG §4.6, step 3 and (4.16)). -/
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {d₁ : ℕ}
    (x : Fin d₁ → ι → ℂ) (y : ι → ι → ℂ) (k₀ : ι) {d₀ : ℕ} (hd₀ : d₀ ≤ 1) {cx cy : ℝ}
    (hcx : ∑ i, ∑ ν, ‖x i ν‖ ≤ cx) (hcy : ∑ j, ‖y j‖ ≤ cy) {S₁ T : ℕ} {E U N : ℝ}
    (hS₁ : 1 ≤ S₁) (hT : 1 ≤ T) (hU : 0 < U) (hN : 0 < N)
    (hSL : 12 * (Fintype.card ι : ℝ) ^ 2 ≤ N + U + U ∧ Real.exp 1 ≤ E ∧
      E ≤ Real.exp ((N + U + U) / 6) ∧
      ((T : ℝ) + 1) ^ (d₀ + d₁) * (E * ((cy + 2) * S₁)) ^ T *
        Real.exp (cx * T * (E * ((cy + 2) * S₁))) ≤ Real.exp U ∧
      (2 * (N + U + U)) ^ (Fintype.card ι + 1) ≤
        ((T : ℝ) + 1) ^ (d₀ + d₁) * N * Real.log E ^ Fintype.card ι) :
    ∃ p : Fin (d₀ * T + 1) × (Fin d₁ → Fin (T + 1)) → ℤ, p ≠ 0 ∧
      (∀ l, |(p l : ℝ)| ≤ Real.exp N) ∧
      (∀ (s : ι → Fin S₁) (k : ℕ) (L : Fin k → ι),
        ‖iteratedFDeriv ℂ k (fun z : ι → ℂ => ∑ l, (p l : ℂ) * (z k₀ ^ (l.1 : ℕ) *
          Complex.exp (∑ ν, (∑ i, ((l.2 i : ℕ) : ℂ) * x i ν) * z ν))) (∑ j, ((s j : ℕ) : ℂ) • y j)
          (fun l => Pi.single (L l) 1)‖ ≤ k.factorial * Real.exp (-U)) ∧
      ∀ ρ : ℝ, 1 ≤ ρ → ∀ w : ι → ℂ, ‖w‖ ≤ ρ →
        ‖∑ l, (p l : ℂ) * (w k₀ ^ (l.1 : ℕ) *
          Complex.exp (∑ ν, (∑ i, ((l.2 i : ℕ) : ℂ) * x i ν) * w ν))‖ ≤
          ((T : ℝ) + 1) ^ (d₀ + d₁) * Real.exp N * ρ ^ T * Real.exp (cx * T * ρ) := by
  classical
  obtain ⟨hP1, hP2, hP3, hP4, hP5⟩ := hSL
  have hT₀T : d₀ * T ≤ T := by
    calc d₀ * T ≤ 1 * T := Nat.mul_le_mul_right _ hd₀
      _ = T := one_mul T
  /- The exponential monomials and their growth. -/
  set φ : Fin (d₀ * T + 1) × (Fin d₁ → Fin (T + 1)) → (ι → ℂ) → ℂ := fun l z =>
    z k₀ ^ (l.1 : ℕ) * Complex.exp (∑ ν, (∑ i, ((l.2 i : ℕ) : ℂ) * x i ν) * z ν) with hφ_def
  have hφan : ∀ l, AnalyticOnNhd ℂ (φ l) Set.univ := fun l => analytic_expMono k₀ _ _
  have hφbound : ∀ l, ∀ Rb : ℝ, 1 ≤ Rb → ∀ z : ι → ℂ, ‖z‖ ≤ Rb →
      ‖φ l z‖ ≤ Rb ^ T * Real.exp (cx * T * Rb) := by
    intro l Rb hRb z hz
    have hc : ∑ ν, ‖∑ i, ((l.2 i : ℕ) : ℂ) * x i ν‖ ≤ cx * T := by
      calc ∑ ν, ‖∑ i, ((l.2 i : ℕ) : ℂ) * x i ν‖ ≤ ∑ ν, ∑ i, (T : ℝ) * ‖x i ν‖ :=
            Finset.sum_le_sum fun ν _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => by
              rw [norm_mul, Complex.norm_natCast]
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.lt_succ_iff.mp (l.2 i).2)
                (norm_nonneg _))
        _ = (∑ i, ∑ ν, ‖x i ν‖) * T := by
            rw [Finset.sum_comm, Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]; simp [mul_comm]
        _ ≤ cx * T := mul_le_mul_of_nonneg_right hcx (by positivity)
    exact norm_expMono_le k₀ ((Nat.lt_succ_iff.mp l.1.2).trans hT₀T) _ hRb hc hz
  have hcardΛ : (Fintype.card (Fin (d₀ * T + 1) × (Fin d₁ → Fin (T + 1))) : ℝ) =
      ((T : ℝ) + 1) ^ (d₀ + d₁) := by
    rw [card_Λ hd₀]; push_cast; ring
  /- Book's step 3: node 3 with `r = (cy + 2) S₁` and `R = E r`. -/
  have hcy0 : 0 ≤ cy := le_trans (Finset.sum_nonneg fun j _ => norm_nonneg _) hcy
  set r : ℝ := (cy + 2) * S₁ with hr_def
  have hrpos : 0 < r := by positivity
  set R : ℝ := E * r with hR_def
  have hE1 : 1 ≤ E := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hP2
  have hR1 : 1 ≤ R := by
    have hr1 : 1 ≤ r := by
      have : (1 : ℝ) ≤ S₁ := by exact_mod_cast hS₁
      rw [hr_def]; nlinarith
    exact one_le_mul_of_one_le_of_one_le hE1 hr1
  obtain ⟨p, hp0, hpN, hsmall⟩ := Transcendence.siegel_small_values (ι := ι)
    (N := N) (U := U) (V := U) (r := r) (R := R)
    (Fintype.card_pos_iff.mpr ⟨k₀⟩) φ hφan hN hU hU hrpos hP1
    (by rw [hR_def]; exact mul_le_mul_of_nonneg_right hP2 hrpos.le)
    (by rw [hR_def, mul_comm r]; exact mul_le_mul_of_nonneg_right hP3 hrpos.le)
    (fun _ => R ^ T * Real.exp (cx * T * R))
    (fun l z hz => hφbound l R hR1 z (by simpa using hz))
    (by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardΛ, ← mul_assoc]
      exact hP4)
    (by
      rw [hcardΛ, hR_def, mul_div_assoc, div_self hrpos.ne', mul_one]
      exact hP5)
  have hFan : AnalyticOnNhd ℂ (fun z => ∑ l, (p l : ℂ) * φ l z) Set.univ := by
    intro z _
    have : (fun z => ∑ l, (p l : ℂ) * φ l z) = ∑ l, fun z => (p l : ℂ) * φ l z := by
      funext z; simp
    rw [this]
    exact Finset.analyticAt_sum _ fun l _ => analyticAt_const.mul (hφan l z trivial)
  refine ⟨p, hp0, hpN, fun s k L => ?_, fun ρ hρ w hw => ?_⟩
  · /- (4.16): Cauchy's inequality on the unit polydisc at the grid point, where `|F| ≤ e^{-U}`. -/
    have hqnorm : ‖∑ j, ((s j : ℕ) : ℂ) • y j‖ ≤ S₁ * cy := by
      calc ‖∑ j, ((s j : ℕ) : ℂ) • y j‖ ≤ ∑ j, ‖((s j : ℕ) : ℂ) • y j‖ := norm_sum_le _ _
        _ ≤ ∑ j, (S₁ : ℝ) * ‖y j‖ := Finset.sum_le_sum fun j _ => by
            rw [norm_smul, Complex.norm_natCast]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast (s j).2.le) (norm_nonneg _)
        _ = S₁ * ∑ j, ‖y j‖ := by rw [← Finset.mul_sum]
        _ ≤ S₁ * cy := mul_le_mul_of_nonneg_left hcy (by positivity)
    have hball : closedBall (∑ j, ((s j : ℕ) : ℂ) • y j) 1 ⊆ closedBall (0 : ι → ℂ) r := by
      intro w hw
      rw [mem_closedBall, dist_eq_norm] at hw
      rw [mem_closedBall_zero_iff]
      calc ‖w‖ ≤ ‖∑ j, ((s j : ℕ) : ℂ) • y j‖ + ‖w - ∑ j, ((s j : ℕ) : ℂ) • y j‖ := by
            have := norm_add_le (∑ j, ((s j : ℕ) : ℂ) • y j) (w - ∑ j, ((s j : ℕ) : ℂ) • y j)
            simpa using this
        _ ≤ S₁ * cy + 1 := by linarith
        _ ≤ r := by
            have : (1 : ℝ) ≤ S₁ := by exact_mod_cast hS₁
            rw [hr_def]; nlinarith
    have h := Transcendence.polydisc_cauchy hFan _ one_pos (fun z hz => hsmall z (hball hz)) k L
    rw [one_pow, div_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right (prod_count_factorial_le L) (Real.exp_pos _).le)
  · /- The growth of `F`. -/
    calc ‖∑ l, (p l : ℂ) * φ l w‖ ≤ ∑ l, ‖(p l : ℂ) * φ l w‖ := norm_sum_le _ _
      _ ≤ ∑ _l : Fin (d₀ * T + 1) × (Fin d₁ → Fin (T + 1)),
          Real.exp N * (ρ ^ T * Real.exp (cx * T * ρ)) := Finset.sum_le_sum fun l _ => by
          rw [norm_mul, Complex.norm_intCast]
          exact mul_le_mul (hpN l) (hφbound l ρ hρ w hw) (norm_nonneg _) (Real.exp_pos _).le
      _ = ((T : ℝ) + 1) ^ (d₀ + d₁) * Real.exp N * ρ ^ T * Real.exp (cx * T * ρ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardΛ]; ring

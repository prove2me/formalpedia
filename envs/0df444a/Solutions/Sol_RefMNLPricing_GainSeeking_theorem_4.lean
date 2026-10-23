-- Prove2me | solution 1 for RefMNLPricing.GainSeeking.theorem_4
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T12:52:15.693541+00:00
-- url     : https://prove2.me/submissions/81e7d363-dd64-4600-b2ac-38d3457fe968

import Mathlib
import Definitions.Def_RefMNLPricing_GainSeeking_Model

set_option autoImplicit false

namespace Cex286851ea

open RefMNLPricing

/-- Counterexample data: one product, `a = 51/50`, `b = 1`, `c⁺ = 11/10`, `c⁻ = 1`,
`α = 0`, `β = 3/4`, `p_H = 51/50`, steady state `x = p_H`. -/
noncomputable def A : Fin 1 → ℝ := fun _ => 51/50
noncomputable def Bv : Fin 1 → ℝ := fun _ => 1
noncomputable def CP : Fin 1 → ℝ := fun _ => 11/10
noncomputable def CM : Fin 1 → ℝ := fun _ => 1
noncomputable def X : Fin 1 → ℝ := fun _ => 51/50

/-- The one-step Bellman inequality behind the linear value certificate
`W(r) = 51/25 - (1/8)(51/50 - r)`. -/
theorem step (p r : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 51/50) (hr0 : 0 ≤ r) (hr1 : r ≤ 51/50) :
    p * (Real.exp (51/50 - 1 * p + 11/10 * max (r - p) 0 - 1 * max (p - r) 0) /
      (1 + Real.exp (51/50 - 1 * p + 11/10 * max (r - p) 0 - 1 * max (p - r) 0)))
    ≤ 51/100 - 1/8 * (51/50 - r) + 3/32 * (51/50 - p) := by
  set u := 51/50 - 1 * p + 11/10 * max (r - p) 0 - 1 * max (p - r) 0 with hu
  set R := 51/100 - 1/8 * (51/50 - r) + 3/32 * (51/50 - p) with hR
  have hR0 : 0 ≤ R := by rw [hR]; linarith
  have hE : 0 < Real.exp u := Real.exp_pos u
  have hF0 : 0 < Real.exp (-u) := Real.exp_pos _
  have hF : 1 - u ≤ Real.exp (-u) := by have := Real.add_one_le_exp (-u); linarith
  have hEF : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have key : p ≤ R * (1 + Real.exp (-u)) := by
    rcases le_or_gt p R with h | h
    · nlinarith [mul_nonneg hR0 hF0.le]
    · have h2 : p ≤ R * (2 - u) := by
        rcases le_total p r with hpr | hpr
        · have e1 : max (r - p) 0 = r - p := max_eq_left (by linarith)
          have e2 : max (p - r) 0 = 0 := max_eq_right (by linarith)
          rw [hu, e1, e2]; rw [hR] at h ⊢
          nlinarith [mul_nonneg hp0 (sub_nonneg.2 hpr), mul_nonneg (sub_nonneg.2 hpr)
            (sub_nonneg.2 hr1), mul_nonneg hp0 (sub_nonneg.2 hr1), mul_nonneg hp0 hp0,
            mul_nonneg (sub_nonneg.2 hpr) (sub_nonneg.2 hpr)]
        · have e1 : max (r - p) 0 = 0 := max_eq_right (by linarith)
          have e2 : max (p - r) 0 = p - r := max_eq_left (by linarith)
          rw [hu, e1, e2]; rw [hR] at h ⊢
          nlinarith [mul_nonneg hr0 (sub_nonneg.2 hpr), mul_nonneg (sub_nonneg.2 hpr)
            (sub_nonneg.2 hp1), mul_nonneg hr0 (sub_nonneg.2 hp1), mul_nonneg hr0 hr0,
            mul_nonneg (sub_nonneg.2 hpr) (sub_nonneg.2 hpr)]
      nlinarith [mul_le_mul_of_nonneg_left hF hR0]
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left key hE.le, hEF]

theorem rev_eq (P Rv : Fin 1 → ℝ) : Myopic.revenue A Bv CP CM P Rv =
    P 0 * (Real.exp (51/50 - 1 * P 0 + 11/10 * max (Rv 0 - P 0) 0 - 1 * max (P 0 - Rv 0) 0) /
      (1 + Real.exp (51/50 - 1 * P 0 + 11/10 * max (Rv 0 - P 0) 0 - 1 * max (P 0 - Rv 0) 0))) := by
  simp only [Myopic.revenue, Myopic.share, Myopic.util, Fin.sum_univ_one, A, Bv, CP, CM]

theorem chi_eq : Myopic.chi A Bv CP CM = 1/2 := by
  simp only [Myopic.chi, Bv, CP, CM]
  rw [ciSup_const]; norm_num

theorem ceil_eq (p : ℝ) : Myopic.ceilRHS A Bv CP CM p =
    1/2 + 1/(1 + 11/10) * Real.exp (51/50 - 1 * p + (1 + 11/10) * (1/2) - 1) := by
  simp only [Myopic.ceilRHS, chi_eq, Fin.sum_univ_one, A, Bv, CP]

theorem exp_small : Real.exp (1/20) ≤ 20/19 := by
  have h1 : 1 - 1/20 ≤ Real.exp (-(1/20)) := by
    have := Real.add_one_le_exp (-(1/20 : ℝ)); linarith
  have h2 : Real.exp (1/20) * Real.exp (-(1/20)) = 1 := by rw [← Real.exp_add]; simp
  have h3 : 0 < Real.exp (1/20) := Real.exp_pos _
  nlinarith

theorem ceilOK : Gap.CeilingOK A Bv CP CM (51/50) := by
  set f : ℝ → ℝ := fun p => p - (1/2 + 1/(1 + 11/10) * Real.exp (51/50 - 1 * p + (1 + 11/10) * (1/2) - 1))
    with hf
  have hc : ContinuousOn f (Set.Icc (1/2) (51/50)) := by
    rw [hf]; exact Continuous.continuousOn (by fun_prop)
  have h0 : f (1/2) ≤ 0 := by
    rw [hf]; simp only
    have := Real.exp_pos (51/50 - 1 * (1/2:ℝ) + (1 + 11/10) * (1/2) - 1)
    nlinarith
  have h1 : 0 ≤ f (51/50) := by
    rw [hf]; simp only
    have e : (51/50 - 1 * (51/50:ℝ) + (1 + 11/10) * (1/2) - 1) = 1/20 := by norm_num
    rw [e]
    have := exp_small
    nlinarith
  obtain ⟨c, hcI, hfc⟩ := intermediate_value_Icc (by norm_num) hc ⟨h0, h1⟩
  refine ⟨c, ?_, hcI.2⟩
  rw [ceil_eq]
  rw [hf] at hfc; simp only at hfc
  linarith

theorem disc_le (p : ℕ → Fin 1 → Set.Icc (0:ℝ) (51/50)) :
    Gap.disc A Bv CP CM 0 (3/4) (fun t i => (p t i : ℝ)) X ≤ 51/25 := by
  set P : ℕ → Fin 1 → ℝ := fun t i => (p t i : ℝ) with hP
  set r : ℕ → ℝ := fun t => Gap.refPath 0 X P t 0 with hr
  have hr0 : r 0 = 51/50 := by simp [hr, Gap.refPath, X]
  have hrs : ∀ t, r (t+1) = P t 0 := by intro t; simp [hr, Gap.refPath]
  have hPb : ∀ t, 0 ≤ P t 0 ∧ P t 0 ≤ 51/50 := fun t => (p t 0).2
  have hrb : ∀ t, 0 ≤ r t ∧ r t ≤ 51/50 := by
    intro t
    cases t with
    | zero => rw [hr0]; norm_num
    | succ t => rw [hrs]; exact hPb t
  have hstep : ∀ t, Myopic.revenue A Bv CP CM (P t) (Gap.refPath 0 X P t) ≤
      51/100 - 1/8 * (51/50 - r t) + 3/32 * (51/50 - r (t+1)) := by
    intro t
    rw [rev_eq, hrs]
    exact step (P t 0) (r t) (hPb t).1 (hPb t).2 (hrb t).1 (hrb t).2
  have hnn : ∀ t, 0 ≤ (3/4:ℝ)^t * Myopic.revenue A Bv CP CM (P t) (Gap.refPath 0 X P t) := by
    intro t
    rw [rev_eq]
    have := (hPb t).1
    positivity
  have inv : ∀ N, ∑ t ∈ Finset.range N, (3/4:ℝ)^t * Myopic.revenue A Bv CP CM (P t) (Gap.refPath 0 X P t)
      ≤ 51/25 - (3/4)^N * (51/25) + 1/8 * (3/4)^N * (51/50 - r N) := by
    intro N
    induction N with
    | zero => simp [hr0]
    | succ N ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have h := hstep N
      have hy : 0 ≤ (3/4:ℝ)^N := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h hy]
  unfold Gap.disc
  apply Real.tsum_le_of_sum_range_le hnn
  intro N
  have h := inv N
  have hy : 0 ≤ (3/4:ℝ)^N := by positivity
  have := hrb N
  nlinarith

theorem steady_val : Myopic.revenue A Bv CP CM X X / (1 - 3/4) = 51/25 := by
  rw [rev_eq]; simp [X]; norm_num

end Cex286851ea

open RefMNLPricing.GainSeeking in
theorem solution : ¬ (∀ {n : ℕ} (a b cp cm : Fin n → ℝ) (α β pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Ico (0 : ℝ) 1) (hpH : 0 < pH)
    (hceil : RefMNLPricing.Gap.CeilingOK a b cp cm pH)
    (hgain : ∃ i, IsGainSeeking cp cm i),
    ∀ x : Fin n → ℝ, ¬ IsOptSteadyState a b cp cm α β pH x) := by
  intro h
  refine h Cex286851ea.A Cex286851ea.Bv Cex286851ea.CP Cex286851ea.CM 0 (3/4) (51/50)
    (fun _ => by norm_num [Cex286851ea.Bv]) (fun _ => by norm_num [Cex286851ea.CP])
    (fun _ => by norm_num [Cex286851ea.CM]) (by norm_num) (by norm_num) (by norm_num)
    Cex286851ea.ceilOK ⟨0, by norm_num [IsGainSeeking, Cex286851ea.CP, Cex286851ea.CM]⟩
    Cex286851ea.X ⟨?_, ?_⟩
  · intro i; simp only [Cex286851ea.X, Set.mem_Icc]; norm_num
  · rw [Cex286851ea.steady_val]
    unfold optValue
    have : Nonempty (Set.Icc (0:ℝ) (51/50)) := ⟨⟨0, by norm_num⟩⟩
    apply ciSup_le
    intro p
    exact Cex286851ea.disc_le p

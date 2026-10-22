-- Prove2me | solution 1 for SubstitutePricing.Mixed.eq_31_strict_concave
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:27:58.731391+00:00
-- url     : https://prove2.me/submissions/20da4fea-7a2d-4f29-b967-eb395bf36733

import Mathlib
import Definitions.Def_SubstitutePricing_Mixed_Model

set_option autoImplicit false

open SubstitutePricing.Mixed

theorem solution (M : Model) (hM : M.Assumptions) (x : Fin M.n → ℕ)
    (δ : Fin M.n → ℝ) :
    StrictConcaveOn ℝ (M.probDomain x) (M.xiProb x δ) := by
  have hΘ : 0 ≤ M.Θ x := Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le)
  have hμ := hM.mu_pos
  have hl := hM.lam_pos
  have h2 : 0 < 1 + M.Θ x := by linarith
  set S := M.S1 x with hS
  set c : Fin M.n → ℝ := fun i =>
    M.lam * (M.a i - M.u0 - δ i) - M.lam * M.μ * Real.log (1 + M.Θ x) with hc
  set κ : ℝ := (∑ j ∈ M.S2 x, M.lam * M.θ j * (M.rfix j - δ j)) / (1 + M.Θ x) with hκ
  set G : ℝ → ℝ := fun t => Real.log t + Real.negMulLog t with hG
  have hGc : ConcaveOn ℝ (Set.Ioi 0) G :=
    strictConcaveOn_log_Ioi.concaveOn.add
      (Real.concaveOn_negMulLog.subset (fun t ht => Set.mem_Ici.2 (le_of_lt ht)) (convex_Ioi 0))
  have key : ∀ p ∈ M.probDomain x, M.xiProb x δ p =
      (∑ i ∈ S, p i * c i + κ * (1 - ∑ i ∈ S, p i)) +
        M.lam * M.μ * ((∑ i ∈ S, Real.negMulLog (p i)) + G (1 - ∑ i ∈ S, p i)) := by
    intro p hp
    obtain ⟨hp0, hs, -⟩ := hp
    have h1 : 0 < 1 - ∑ i ∈ S, p i := by linarith
    have hlog : Real.log (M.P0of x p) = Real.log (1 - ∑ i ∈ S, p i) - Real.log (1 + M.Θ x) := by
      unfold Model.P0of; rw [Real.log_div h1.ne' h2.ne']
    have e1 : ∀ i ∈ S, M.lam * p i *
        (M.a i - M.u0 - M.μ * Real.log (p i) + M.μ * Real.log (M.P0of x p) - δ i) =
        p i * c i + M.lam * M.μ * Real.negMulLog (p i) +
          M.lam * M.μ * (p i * Real.log (1 - ∑ i ∈ S, p i)) := by
      intro i _
      rw [hlog, hc]; simp only [Real.negMulLog]; ring
    have e2 : ∑ j ∈ M.S2 x, M.lam * (M.θ j * M.P0of x p) * (M.rfix j - δ j) =
        κ * (1 - ∑ i ∈ S, p i) := by
      rw [hκ, Finset.sum_div, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      unfold Model.P0of
      simp only [← hS]
      field_simp
      try ring
    unfold Model.xiProb
    rw [Finset.sum_congr rfl e1, e2, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
    have : G (1 - ∑ i ∈ S, p i) = (∑ i ∈ S, p i) * Real.log (1 - ∑ i ∈ S, p i) := by
      simp only [hG, Real.negMulLog]; ring
    rw [this]; ring
  have hconv : Convex ℝ (M.probDomain x) := by
    intro p hp q hq a b ha hb hab
    obtain ⟨hp0, hps, hp1⟩ := hp
    obtain ⟨hq0, hqs, hq1⟩ := hq
    have hsum : ∑ i ∈ S, (a • p + b • q) i = a * ∑ i ∈ S, p i + b * ∑ i ∈ S, q i := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hp0 i hi; have := hq0 i hi
      rcases ha.eq_or_lt with rfl | ha'
      · have : b = 1 := by linarith
        subst this; simpa using hq0 i hi
      · nlinarith [mul_pos ha' (hp0 i hi), mul_nonneg hb (hq0 i hi).le]
    · change ∑ i ∈ S, (a • p + b • q) i < 1
      rw [hsum]
      rcases ha.eq_or_lt with rfl | ha'
      · have : b = 1 := by linarith
        subst this; simpa using hqs
      · nlinarith [mul_pos ha' (sub_pos.2 hps), mul_nonneg hb (sub_pos.2 hqs).le]
    · intro i hi
      simp [hp1 i hi, hq1 i hi]
  refine ⟨hconv, ?_⟩
  intro p hp q hq hpq a b ha hb hab
  have hr : a • p + b • q ∈ M.probDomain x := hconv hp hq ha.le hb.le hab
  rw [key p hp, key q hq, key _ hr]
  simp only [smul_eq_mul]
  have hsum : ∑ i ∈ S, (a • p + b • q) i = a * ∑ i ∈ S, p i + b * ∑ i ∈ S, q i := by
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  have hlin : ∑ i ∈ S, (a • p + b • q) i * c i =
      a * ∑ i ∈ S, p i * c i + b * ∑ i ∈ S, q i * c i := by
    simp [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  have hp1 : 0 < 1 - ∑ i ∈ S, p i := by linarith [hp.2.1]
  have hq1 : 0 < 1 - ∑ i ∈ S, q i := by linarith [hq.2.1]
  have hG' := hGc.2 (Set.mem_Ioi.2 hp1) (Set.mem_Ioi.2 hq1) ha.le hb.le hab
  have hrw : 1 - ∑ i ∈ S, (a • p + b • q) i =
      a * (1 - ∑ i ∈ S, p i) + b * (1 - ∑ i ∈ S, q i) := by
    rw [hsum]; linear_combination (-(1:ℝ)) * hab
  rw [hrw, hlin]
  simp only [smul_eq_mul] at hG'
  have hlm : 0 < M.lam * M.μ := mul_pos hl hμ
  have hpt : ∀ i, (a • p + b • q) i = a * p i + b * q i := by intro i; simp
  have hH2 : a * ∑ i ∈ S, Real.negMulLog (p i) + b * ∑ i ∈ S, Real.negMulLog (q i) <
      ∑ i ∈ S, Real.negMulLog ((a • p + b • q) i) := by
    have hne : ∃ i ∈ S, p i ≠ q i := by
      by_contra hcon
      push_neg at hcon
      apply hpq
      funext i
      by_cases hi : i ∈ S
      · exact hcon i hi
      · rw [hp.2.2 i hi, hq.2.2 i hi]
    obtain ⟨i0, hi0, hne⟩ := hne
    have hle : ∀ i ∈ S, a * Real.negMulLog (p i) + b * Real.negMulLog (q i) ≤
        Real.negMulLog ((a • p + b • q) i) := fun i hi => by
      have := Real.concaveOn_negMulLog.2 (Set.mem_Ici.2 (hp.1 i hi).le)
        (Set.mem_Ici.2 (hq.1 i hi).le) ha.le hb.le hab
      rw [hpt]; simpa [smul_eq_mul] using this
    have hlt : a * Real.negMulLog (p i0) + b * Real.negMulLog (q i0) <
        Real.negMulLog ((a • p + b • q) i0) := by
      have := Real.strictConcaveOn_negMulLog.2 (Set.mem_Ici.2 (hp.1 i0 hi0).le)
        (Set.mem_Ici.2 (hq.1 i0 hi0).le) hne ha hb hab
      rw [hpt]; simpa [smul_eq_mul] using this
    calc a * ∑ i ∈ S, Real.negMulLog (p i) + b * ∑ i ∈ S, Real.negMulLog (q i)
        = ∑ i ∈ S, (a * Real.negMulLog (p i) + b * Real.negMulLog (q i)) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      _ < _ := Finset.sum_lt_sum hle ⟨i0, hi0, hlt⟩
  have h3 := mul_lt_mul_of_pos_left hH2 hlm
  have h4 := mul_le_mul_of_nonneg_left hG' hlm.le
  nlinarith [h3, h4]

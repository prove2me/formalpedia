-- Prove2me | solution 2 for StatComplexityDM.Disagreement.posterior_sampling_sq_dec_disagreement
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T07:31:20.654692+00:00
-- url     : https://prove2.me/submissions/8d613810-b4ff-49d0-9ff2-c91ac15d8330

import Mathlib
import Definitions.Def_StatComplexityDM_Disagreement_Coefficient
import Theorems.Thm_StatComplexityDM_Disagreement_decoupling_disagreement

-- carved verbatim out of submission 2f7d154c-55c2-4cdc-aa9d-001246b3ce44, lines 461-538

section
set_option autoImplicit false
open StatComplexityDM.Disagreement

lemma SCD_bdd {κ Act : Type*} [Fintype κ] (F : Set (Act → ℝ)) (R : ℝ)
    (hF : ∀ f ∈ F, ∀ π, |f π| ≤ R) (ρw : κ → ℝ) (ρpt : κ → Act)
    (hρ : StatComplexityDM.LowerBound.IsDist ρw) (Δ₀ ε₀ : ℝ) (hΔ₀ : 0 < Δ₀) (hε₀ : 0 < ε₀) :
    BddAbove {x : ℝ | ∃ Δ ε : ℝ, Δ₀ ≤ Δ ∧ ε₀ ≤ ε ∧
      x = Δ ^ 2 / ε ^ 2 * distProb ρw ρpt (disagreeEvent F Δ ε ρw ρpt)} := by
  obtain ⟨hnn, hsum⟩ := hρ
  have hp01 : ∀ A : Act → Prop, 0 ≤ distProb ρw ρpt A ∧ distProb ρw ρpt A ≤ 1 := by
    intro A
    unfold distProb
    constructor
    · apply Finset.sum_nonneg
      intro k _
      exact mul_nonneg (hnn k) (by split_ifs <;> norm_num)
    · calc _ ≤ ∑ k, ρw k * 1 := by
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_left (by split_ifs <;> norm_num) (hnn k)
        _ = 1 := by simp [hsum]
  refine ⟨R ^ 2 / ε₀ ^ 2, ?_⟩
  rintro x ⟨Δ, e, hΔ, he, rfl⟩
  obtain ⟨hp0, hp1⟩ := hp01 (disagreeEvent F Δ e ρw ρpt)
  by_cases hR : Δ < R
  · have hΔpos : 0 < Δ := lt_of_lt_of_le hΔ₀ hΔ
    have hepos : 0 < e := lt_of_lt_of_le hε₀ he
    have h1 : Δ ^ 2 / e ^ 2 ≤ R ^ 2 / ε₀ ^ 2 := by
      apply div_le_div₀ (sq_nonneg R) _ (by positivity) _
      · nlinarith
      · exact pow_le_pow_left₀ hε₀.le he 2
    calc Δ ^ 2 / e ^ 2 * distProb ρw ρpt (disagreeEvent F Δ e ρw ρpt)
        ≤ Δ ^ 2 / e ^ 2 * 1 := mul_le_mul_of_nonneg_left hp1 (by positivity)
      _ ≤ R ^ 2 / ε₀ ^ 2 := by linarith
  · have hempty : distProb ρw ρpt (disagreeEvent F Δ e ρw ρpt) = 0 := by
      unfold distProb
      apply Finset.sum_eq_zero
      intro k _
      have : ¬ disagreeEvent F Δ e ρw ρpt (ρpt k) := by
        rintro ⟨f, hf, h1, _⟩
        have := hF f hf (ρpt k)
        linarith [not_lt.1 hR]
      simp [this]
    rw [hempty]
    simp only [mul_zero]
    positivity

lemma SCD_mono {κ Act : Type*} [Fintype κ] (F : Set (Act → ℝ)) (R : ℝ)
    (hF : ∀ f ∈ F, ∀ π, |f π| ≤ R) (ρw : κ → ℝ) (ρpt : κ → Act)
    (hρ : StatComplexityDM.LowerBound.IsDist ρw) (Δ₀ ε₀ ε₁ : ℝ) (hΔ₀ : 0 < Δ₀) (hε₀ : 0 < ε₀)
    (h : ε₀ ≤ ε₁) :
    disagreementCoeff F Δ₀ ε₁ ρw ρpt ≤ disagreementCoeff F Δ₀ ε₀ ρw ρpt := by
  unfold disagreementCoeff
  apply max_le_max _ le_rfl
  apply csSup_le_csSup (SCD_bdd F R hF ρw ρpt hρ Δ₀ ε₀ hΔ₀ hε₀)
  · exact ⟨_, Δ₀, ε₁, le_rfl, le_rfl, rfl⟩
  · rintro x ⟨Δ, e, hΔ, he, rfl⟩
    exact ⟨Δ, e, hΔ, h.trans he, rfl⟩

lemma SCD_fixed {ι Act : Type*} [Fintype ι] (FM : Set (Act → ℝ))
    (hF : ∀ f ∈ FM, ∀ π, 0 ≤ f π ∧ f π ≤ 1) (w : ι → ℝ) (hw : StatComplexityDM.LowerBound.IsDist w)
    (fM : ι → Act → ℝ) (hfM : ∀ i, fM i ∈ FM) (piM : ι → Act)
    (g : Act → ℝ) (hg : g ∈ FM) (γ : ℝ) (hγ : Real.exp 1 ≤ γ) (Δ : ℝ) (hΔ : 0 < Δ) :
    ∑ i, w i * (fM i (piM i) - g (piM i))
      ≤ 2 * Δ + 24 * disagreementCoeff (shiftClass FM g) Δ γ⁻¹ w piM
          * Real.log (max γ (Real.exp 1)) ^ 2 / γ
        + γ / 4 * ∑ j, w j * ∑ i, w i * (fM i (piM j) - g (piM j)) ^ 2 := by
  have he1 : 2 < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := 1) (by norm_num); linarith
  have hγ0 : 0 < γ := by linarith
  have hγ4 : 0 < γ / 4 := by positivity
  have hFs : ∀ f ∈ shiftClass FM g, ∀ π, |f π| ≤ 1 := by
    rintro f ⟨h, hh, rfl⟩ π
    have h1 := hF h hh π
    have h2 := hF g hg π
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hcore := StatComplexityDM.Disagreement.decoupling_disagreement (shiftClass FM g) 1 le_rfl hFs w hw (fun i π => fM i π - g π)
    (fun i => ⟨fM i, hfM i, rfl⟩) piM (γ / 4) hγ4 Δ hΔ
  have hmono : disagreementCoeff (shiftClass FM g) Δ (γ / 4)⁻¹ w piM ≤
      disagreementCoeff (shiftClass FM g) Δ γ⁻¹ w piM := by
    apply SCD_mono (shiftClass FM g) 1 hFs w piM hw Δ γ⁻¹ _ hΔ (by positivity)
    rw [inv_div]
    have : γ⁻¹ = 1 / γ := one_div γ |>.symm
    rw [this]
    rw [div_le_div_iff₀ hγ0 hγ0]
    nlinarith
  have hlog : Real.log (max (1 * (γ / 4)) (Real.exp 1)) ^ 2 ≤ Real.log (max γ (Real.exp 1)) ^ 2 := by
    have h1 : 0 ≤ Real.log (max (1 * (γ / 4)) (Real.exp 1)) := by
      apply Real.log_nonneg
      calc (1:ℝ) ≤ Real.exp 1 := by linarith
        _ ≤ _ := le_max_right _ _
    apply pow_le_pow_left₀ h1
    apply Real.log_le_log (lt_of_lt_of_le (Real.exp_pos 1) (le_max_right _ _))
    apply max_le_max _ le_rfl
    linarith
  have hθ1 : 1 ≤ disagreementCoeff (shiftClass FM g) Δ (γ / 4)⁻¹ w piM := le_max_right _ _
  have hlogpos : 0 ≤ Real.log (max (1 * (γ / 4)) (Real.exp 1)) ^ 2 := sq_nonneg _
  have habs : ∑ i, w i * (fM i (piM i) - g (piM i)) ≤ ∑ i, w i * |fM i (piM i) - g (piM i)| := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (le_abs_self _) (hw.1 i)
  have hconst : 6 * disagreementCoeff (shiftClass FM g) Δ (γ / 4)⁻¹ w piM *
      Real.log (max (1 * (γ / 4)) (Real.exp 1)) ^ 2 / (γ / 4) ≤
      24 * disagreementCoeff (shiftClass FM g) Δ γ⁻¹ w piM * Real.log (max γ (Real.exp 1)) ^ 2 / γ := by
    have hθ0 : 0 ≤ disagreementCoeff (shiftClass FM g) Δ (γ / 4)⁻¹ w piM := by linarith
    have e1 : 6 * disagreementCoeff (shiftClass FM g) Δ (γ / 4)⁻¹ w piM *
        Real.log (max (1 * (γ / 4)) (Real.exp 1)) ^ 2 / (γ / 4) =
        24 * disagreementCoeff (shiftClass FM g) Δ (γ / 4)⁻¹ w piM *
        Real.log (max (1 * (γ / 4)) (Real.exp 1)) ^ 2 / γ := by
      field_simp; ring
    rw [e1]
    apply div_le_div_of_nonneg_right _ hγ0.le
    have hθ'1 : 1 ≤ disagreementCoeff (shiftClass FM g) Δ γ⁻¹ w piM := le_max_right _ _
    apply mul_le_mul _ hlog hlogpos (by linarith)
    nlinarith
  have hsq : ∑ i, w i * ∑ j, w j * (fM i (piM j) - g (piM j)) ^ 2 =
      ∑ j, w j * ∑ i, w i * (fM i (piM j) - g (piM j)) ^ 2 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro i _
    ring
  have hcore' : ∑ i, w i * |fM i (piM i) - g (piM i)| ≤ 2 * Δ +
      6 * disagreementCoeff (shiftClass FM g) Δ (γ / 4)⁻¹ w piM *
        Real.log (max (1 * (γ / 4)) (Real.exp 1)) ^ 2 / (γ / 4) +
      γ / 4 * ∑ i, w i * ∑ j, w j * (fM i (piM j) - g (piM j)) ^ 2 := hcore
  rw [hsq] at hcore'
  linarith

lemma SCD_swap {ι : Type*} [Fintype ι] (w : ι → ℝ) (X : ι → ι → ℝ) :
    ∑ i, w i * ∑ k, w k * X i k = ∑ k, w k * ∑ i, w i * X i k := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

lemma SCD_lin {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw1 : ∑ i, w i = 1) (T : ι → ℝ) (c d : ℝ) :
    ∑ m, w m * (c + d * T m) = c + d * ∑ m, w m * T m := by
  have : ∀ m, w m * (c + d * T m) = c * w m + d * (w m * T m) := by intro m; ring
  simp only [this, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, hw1]; ring

lemma SCD_sq4 {ι Act : Type*} [Fintype ι] (w : ι → ℝ) (hw : StatComplexityDM.LowerBound.IsDist w)
    (fM : ι → Act → ℝ) (fbar : Act → ℝ) (π : Act) :
    ∑ i, w i * ∑ k, w k * (fM i π - fM k π) ^ 2 ≤ 4 * ∑ i, w i * (fM i π - fbar π) ^ 2 := by
  obtain ⟨h0, h1⟩ := hw
  have key : ∀ i, ∑ k, w k * (fM i π - fM k π) ^ 2 ≤
      2 * (fM i π - fbar π) ^ 2 + 2 * ∑ k, w k * (fM k π - fbar π) ^ 2 := by
    intro i
    calc ∑ k, w k * (fM i π - fM k π) ^ 2
        ≤ ∑ k, w k * (2 * (fM i π - fbar π) ^ 2 + 2 * (fM k π - fbar π) ^ 2) := by
          apply Finset.sum_le_sum
          intro k _
          apply mul_le_mul_of_nonneg_left _ (h0 k)
          nlinarith [sq_nonneg ((fM i π - fbar π) + (fM k π - fbar π))]
      _ = 2 * (fM i π - fbar π) ^ 2 * ∑ k, w k + 2 * ∑ k, w k * (fM k π - fbar π) ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k _
          ring
      _ = _ := by rw [h1]; ring
  calc ∑ i, w i * ∑ k, w k * (fM i π - fM k π) ^ 2
      ≤ ∑ i, w i * (2 * (fM i π - fbar π) ^ 2 + 2 * ∑ k, w k * (fM k π - fbar π) ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (key i) (h0 i)
    _ = 4 * ∑ i, w i * (fM i π - fbar π) ^ 2 := by
        have e : ∀ i, w i * (2 * (fM i π - fbar π) ^ 2 + 2 * ∑ k, w k * (fM k π - fbar π) ^ 2)
            = 2 * (w i * (fM i π - fbar π) ^ 2)
              + (2 * ∑ k, w k * (fM k π - fbar π) ^ 2) * w i := by
          intro i; ring
        simp_rw [e]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1]
        ring

theorem solution {ι Act : Type*} [Fintype ι] (FM : Set (Act → ℝ))
    (hF : ∀ f ∈ FM, ∀ π, 0 ≤ f π ∧ f π ≤ 1) (w : ι → ℝ) (hw : StatComplexityDM.LowerBound.IsDist w) (fM : ι → Act → ℝ)
    (hfM : ∀ i, fM i ∈ FM) (piM : ι → Act) (hpiM : ∀ i π, fM i π ≤ fM i (piM i))
    (fbar : Act → ℝ) (hfbar : ∀ π, 0 ≤ fbar π ∧ fbar π ≤ 1) (γ : ℝ) (hγ : Real.exp 1 ≤ γ) :
    ∀ Δ : ℝ, 0 < Δ → ∀ Θ : ℝ,
      (∀ g ∈ FM, disagreementCoeff (shiftClass FM g) Δ γ⁻¹ w piM ≤ Θ) →
      sqDecObjective w fM piM fbar γ w piM ≤ 2 * Δ + 24 * Θ * Real.log γ ^ 2 / γ := by
  intro Δ hΔ Θ hΘ
  have hw' := hw
  obtain ⟨hw0, hw1⟩ := hw
  have he1 : 2 < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := 1) (by norm_num); linarith
  have hγ0 : 0 < γ := by linarith
  have hlog : Real.log (max γ (Real.exp 1)) = Real.log γ := by rw [max_eq_left hγ]
  set P := ∑ i, w i * fM i (piM i) with hP
  set U : ι → ℝ := fun m => ∑ i, w i * fM m (piM i) with hU
  set T : ι → ℝ := fun m => ∑ j, w j * ∑ i, w i * (fM i (piM j) - fM m (piM j)) ^ 2 with hT
  set Q := ∑ j, w j * ∑ i, w i * (fM i (piM j) - fbar (piM j)) ^ 2 with hQ
  -- fixed-shift bound for each reference model m
  have hfs : ∀ m, ∑ i, w i * (fM i (piM i) - fM m (piM i)) ≤
      2 * Δ + 24 * Θ * Real.log γ ^ 2 / γ + γ / 4 * T m := by
    intro m
    have h1 := SCD_fixed FM hF w hw' fM hfM piM (fM m) (hfM m) γ hγ Δ hΔ
    rw [hlog] at h1
    have h2 := hΘ (fM m) (hfM m)
    have h3 : 24 * disagreementCoeff (shiftClass FM (fM m)) Δ γ⁻¹ w piM * Real.log γ ^ 2 / γ ≤
        24 * Θ * Real.log γ ^ 2 / γ := by
      apply div_le_div_of_nonneg_right _ hγ0.le
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith
    show _ ≤ _ + _ + γ / 4 * (∑ j, w j * ∑ i, w i * (fM i (piM j) - fM m (piM j)) ^ 2)
    linarith
  have havg : ∑ m, w m * ∑ i, w i * (fM i (piM i) - fM m (piM i)) ≤
      ∑ m, w m * (2 * Δ + 24 * Θ * Real.log γ ^ 2 / γ + γ / 4 * T m) :=
    Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left (hfs m) (hw0 m))
  rw [SCD_lin w hw1 T] at havg
  -- the left side
  have hleft : ∑ m, w m * ∑ i, w i * (fM i (piM i) - fM m (piM i)) = P - ∑ m, w m * U m := by
    have e : ∀ m, ∑ i, w i * (fM i (piM i) - fM m (piM i)) = P + (-1) * U m := by
      intro m
      simp only [hP, hU, mul_sub, Finset.sum_sub_distrib]; ring
    simp only [e]
    rw [SCD_lin w hw1 U P (-1)]; ring
  -- quadratic term
  have hquad : ∑ m, w m * T m ≤ 4 * Q := by
    have e1 : ∑ m, w m * T m = ∑ j, w j * ∑ i, w i * ∑ m, w m * (fM i (piM j) - fM m (piM j)) ^ 2 := by
      simp only [hT]
      rw [SCD_swap w (fun m j => ∑ i, w i * (fM i (piM j) - fM m (piM j)) ^ 2)]
      apply Finset.sum_congr rfl; intro j _
      congr 1
      exact SCD_swap w (fun a b => (fM b (piM j) - fM a (piM j)) ^ 2)
    rw [e1, hQ, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have := SCD_sq4 w hw' fM fbar (piM j)
    calc w j * ∑ i, w i * ∑ m, w m * (fM i (piM j) - fM m (piM j)) ^ 2
        ≤ w j * (4 * ∑ i, w i * (fM i (piM j) - fbar (piM j)) ^ 2) :=
          mul_le_mul_of_nonneg_left this (hw0 j)
      _ = 4 * (w j * ∑ i, w i * (fM i (piM j) - fbar (piM j)) ^ 2) := by ring
  -- the objective
  have hobj : sqDecObjective w fM piM fbar γ w piM = P - ∑ m, w m * U m - γ * Q := by
    unfold sqDecObjective
    have e : ∀ i, ∑ k, w k * (fM i (piM i) - fM i (piM k) - γ * (fM i (piM k) - fbar (piM k)) ^ 2) =
        fM i (piM i) - U i - γ * ∑ k, w k * (fM i (piM k) - fbar (piM k)) ^ 2 := by
      intro i
      have e1 : ∀ k, w k * (fM i (piM i) - fM i (piM k) - γ * (fM i (piM k) - fbar (piM k)) ^ 2) =
          w k * fM i (piM i) - w k * fM i (piM k) - γ * (w k * (fM i (piM k) - fbar (piM k)) ^ 2) := by
        intro k; ring
      simp only [e1, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul, ← Finset.mul_sum, hU]
    have e2 : ∀ i, w i * (fM i (piM i) - U i - γ * ∑ k, w k * (fM i (piM k) - fbar (piM k)) ^ 2) =
        w i * fM i (piM i) - w i * U i - γ * (w i * ∑ k, w k * (fM i (piM k) - fbar (piM k)) ^ 2) := by
      intro i; ring
    simp only [e, e2, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [SCD_swap w (fun i k => (fM i (piM k) - fbar (piM k)) ^ 2)]
  rw [hleft] at havg
  rw [hobj]
  nlinarith [hquad, havg]

end

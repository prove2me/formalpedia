-- Prove2me | solution 1 for StatComplexityDM.Disagreement.decoupling_disagreement
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:38:29.262993+00:00
-- url     : https://prove2.me/submissions/7f6a88ca-e78b-41ff-9663-ad873351ec7e

import Mathlib
import Definitions.Def_StatComplexityDM_Disagreement_Coefficient

set_option autoImplicit false
open StatComplexityDM.Disagreement

lemma SCD_prob {κ Act : Type*} [Fintype κ] (F : Set (Act → ℝ)) (R : ℝ)
    (hF : ∀ f ∈ F, ∀ π, |f π| ≤ R) (ρw : κ → ℝ) (ρpt : κ → Act) (hρ : StatComplexityDM.LowerBound.IsDist ρw)
    (Δ₀ ε₀ : ℝ) (hΔ₀ : 0 < Δ₀) (hε₀ : 0 < ε₀) (δ ε : ℝ) (hδ : Δ₀ ≤ δ) (hε : ε₀ ≤ ε) :
    distProb ρw ρpt (disagreeEvent F δ ε ρw ρpt)
      ≤ ε ^ 2 / δ ^ 2 * disagreementCoeff F Δ₀ ε₀ ρw ρpt := by
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
  have hbdd : BddAbove {x : ℝ | ∃ Δ ε : ℝ, Δ₀ ≤ Δ ∧ ε₀ ≤ ε ∧
      x = Δ ^ 2 / ε ^ 2 * distProb ρw ρpt (disagreeEvent F Δ ε ρw ρpt)} := by
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
  have hmem : δ ^ 2 / ε ^ 2 * distProb ρw ρpt (disagreeEvent F δ ε ρw ρpt) ∈
      {x : ℝ | ∃ Δ ε : ℝ, Δ₀ ≤ Δ ∧ ε₀ ≤ ε ∧
      x = Δ ^ 2 / ε ^ 2 * distProb ρw ρpt (disagreeEvent F Δ ε ρw ρpt)} := ⟨δ, ε, hδ, hε, rfl⟩
  have hle : δ ^ 2 / ε ^ 2 * distProb ρw ρpt (disagreeEvent F δ ε ρw ρpt) ≤
      disagreementCoeff F Δ₀ ε₀ ρw ρpt :=
    le_trans (le_csSup hbdd hmem) (le_max_left _ _)
  have hδpos : 0 < δ := lt_of_lt_of_le hΔ₀ hδ
  have hepos : 0 < ε := lt_of_lt_of_le hε₀ hε
  have : distProb ρw ρpt (disagreeEvent F δ ε ρw ρpt) =
      ε ^ 2 / δ ^ 2 * (δ ^ 2 / ε ^ 2 * distProb ρw ρpt (disagreeEvent F δ ε ρw ρpt)) := by
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left hle (by positivity)

lemma SCD_point (a e γ t₀ : ℝ) (J : ℕ) (hγ : 0 < γ) (ht₀ : 0 < t₀) (he : 0 ≤ e)
    (ha : a ≤ 2 ^ J * t₀) :
    a ≤ t₀ + γ * e + ∑ j ∈ Finset.range J,
      (if (2 ^ j * t₀ < a ∧ e ≤ 2 * (2 ^ j * t₀) / γ) then 2 * (2 ^ j * t₀) else 0) := by
  have hsum_nonneg : 0 ≤ ∑ j ∈ Finset.range J,
      (if (2 ^ j * t₀ < a ∧ e ≤ 2 * (2 ^ j * t₀) / γ) then 2 * (2 ^ j * t₀) else 0) :=
    Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)
  have hge : 0 ≤ γ * e := mul_nonneg hγ.le he
  by_cases h0 : a ≤ t₀
  · linarith
  · push Not at h0
    have hJ : 1 ≤ J := by
      by_contra hJ
      have : J = 0 := by omega
      subst this
      simp at ha
      linarith
    have hex : ∃ j, a ≤ 2 ^ (j + 1) * t₀ := ⟨J - 1, by rwa [Nat.sub_add_cancel hJ]⟩
    classical
    have hj : a ≤ 2 ^ (Nat.find hex + 1) * t₀ := Nat.find_spec hex
    have hjlt : Nat.find hex < J := by
      have : Nat.find hex ≤ J - 1 := Nat.find_min' hex (by rwa [Nat.sub_add_cancel hJ])
      omega
    have hjlo : 2 ^ Nat.find hex * t₀ < a := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
      · rw [h]; simpa using h0
      · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
        have e : Nat.find hex - 1 + 1 = Nat.find hex := by omega
        rw [e] at this
        push Not at this
        exact this
    have hj2 : a ≤ 2 * (2 ^ Nat.find hex * t₀) := by
      rw [pow_succ] at hj; linarith
    by_cases hcase : e ≤ 2 * (2 ^ Nat.find hex * t₀) / γ
    · have hle := Finset.single_le_sum (f := fun j => (if (2 ^ j * t₀ < a ∧ e ≤ 2 * (2 ^ j * t₀) / γ)
          then 2 * (2 ^ j * t₀) else (0:ℝ))) (fun j _ => by split_ifs <;> positivity)
          (Finset.mem_range.2 hjlt)
      simp only [if_pos (And.intro hjlo hcase)] at hle
      linarith
    · push Not at hcase
      have : 2 * (2 ^ Nat.find hex * t₀) < γ * e := by
        rw [div_lt_iff₀ hγ] at hcase; linarith
      linarith

lemma SCD_core {ι Act : Type*} [Fintype ι] (F : Set (Act → ℝ)) (R : ℝ)
    (hR : 1 ≤ R) (hF : ∀ f ∈ F, ∀ π, |f π| ≤ R) (w : ι → ℝ) (hw : StatComplexityDM.LowerBound.IsDist w)
    (fz : ι → Act → ℝ) (hfz : ∀ i, fz i ∈ F) (πz : ι → Act) (γ : ℝ) (hγ : 0 < γ)
    (Δ : ℝ) (hΔ : 0 < Δ) :
    ∑ i, w i * |fz i (πz i)|
      ≤ 2 * Δ + 6 * disagreementCoeff F Δ γ⁻¹ w πz * Real.log (max (R * γ) (Real.exp 1)) ^ 2 / γ
        + γ * ∑ i, w i * ∑ j, w j * fz i (πz j) ^ 2 := by
  have hw' := hw
  obtain ⟨hw0, hw1⟩ := hw
  have hA : ∀ i, |fz i (πz i)| ≤ R := fun i => hF _ (hfz i) _
  have hE : ∀ i, 0 ≤ ∑ j, w j * fz i (πz j) ^ 2 :=
    fun i => Finset.sum_nonneg (fun j _ => mul_nonneg (hw0 j) (sq_nonneg _))
  have hEsum : 0 ≤ γ * ∑ i, w i * ∑ j, w j * fz i (πz j) ^ 2 :=
    mul_nonneg hγ.le (Finset.sum_nonneg (fun i _ => mul_nonneg (hw0 i) (hE i)))
  have hθ1 : 1 ≤ disagreementCoeff F Δ γ⁻¹ w πz := le_max_right _ _
  have hRpos : 0 < R := by linarith
  have hLH : ∑ i, w i * |fz i (πz i)| ≤ R := by
    calc ∑ i, w i * |fz i (πz i)| ≤ ∑ i, w i * R :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hA i) (hw0 i))
      _ = R := by rw [← Finset.sum_mul, hw1, one_mul]
  by_cases hcase : R * γ ≤ 6
  · have hL1 : 1 ≤ Real.log (max (R * γ) (Real.exp 1)) := by
      rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) (le_max_right _ _))]
      exact le_max_right _ _
    have h6 : R ≤ 6 / γ := by rw [le_div_iff₀ hγ]; exact hcase
    have h7 : 6 / γ ≤ 6 * disagreementCoeff F Δ γ⁻¹ w πz * Real.log (max (R * γ) (Real.exp 1)) ^ 2 / γ := by
      apply div_le_div_of_nonneg_right _ hγ.le
      nlinarith
    linarith
  · push Not at hcase
    set θ := disagreementCoeff F Δ γ⁻¹ w πz with hθ
    set L := Real.log (R * γ) with hLdef
    have hmax : max (R * γ) (Real.exp 1) = R * γ :=
      max_eq_left (by have := Real.exp_one_lt_d9; linarith)
    rw [hmax, ← hLdef]
    have hL : 1.74 ≤ L := by
      have h6 : Real.log 6 ≤ L := Real.log_le_log (by norm_num) hcase.le
      have : Real.log 6 = Real.log 2 + Real.log 3 := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
      have h2 := Real.log_two_gt_d9
      have h3 : (1.05 : ℝ) ≤ Real.log 3 := by
        rw [Real.le_log_iff_exp_le (by norm_num)]
        have h1 := Real.exp_one_lt_d9
        have h2 : Real.exp (0.05 : ℝ) < 1 / (1 - 0.05) :=
          Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
        have : Real.exp (1.05 : ℝ) = Real.exp 1 * Real.exp 0.05 := by
          rw [← Real.exp_add]; norm_num
        rw [this]
        have hp := Real.exp_pos (0.05 : ℝ)
        nlinarith
      linarith
    set t₀ := max Δ γ⁻¹ with ht₀
    have ht₀pos : 0 < t₀ := lt_max_of_lt_left hΔ
    have hΔt : Δ ≤ t₀ := le_max_left _ _
    have hgt : γ⁻¹ ≤ t₀ := le_max_right _ _
    have hlog2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
    set J : ℕ := ⌈L / Real.log 2⌉₊ with hJ
    have hJ1 : L / Real.log 2 ≤ J := Nat.le_ceil _
    have hJ2 : (J : ℝ) < L / Real.log 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    have hRJ : R ≤ 2 ^ J * t₀ := by
      have h1 : L ≤ J * Real.log 2 := by rwa [div_le_iff₀ (by linarith)] at hJ1
      have h2 : R * γ ≤ 2 ^ J := by
        have : Real.exp L ≤ Real.exp (J * Real.log 2) := Real.exp_le_exp.2 h1
        rwa [hLdef, Real.exp_log (by positivity), Real.exp_nat_mul, Real.exp_log (by norm_num)] at this
      have h3 : R ≤ 2 ^ J * γ⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hγ]; exact h2
      calc R ≤ 2 ^ J * γ⁻¹ := h3
        _ ≤ 2 ^ J * t₀ := mul_le_mul_of_nonneg_left hgt (by positivity)
    have hJnum : 1 + 4 * (J : ℝ) ≤ 6 * L ^ 2 := by
      have : (J : ℝ) < L / Real.log 2 + 1 := hJ2
      have h5 : L / Real.log 2 ≤ L / 0.6931471803 :=
        div_le_div_of_nonneg_left (by linarith) (by norm_num) hlog2.le
      have h6 : L / 0.6931471803 ≤ 1.443 * L := by
        rw [div_le_iff₀ (by norm_num)]; nlinarith
      nlinarith [mul_nonneg (sub_nonneg.2 hL) (by linarith : (0:ℝ) ≤ L)]
    -- the pointwise bounds
    have hpt : ∀ i, |fz i (πz i)| ≤ t₀ + γ * (∑ j, w j * fz i (πz j) ^ 2) + ∑ j ∈ Finset.range J,
        (if (2 ^ j * t₀ < |fz i (πz i)| ∧ (∑ k, w k * fz i (πz k) ^ 2) ≤ 2 * (2 ^ j * t₀) / γ)
          then 2 * (2 ^ j * t₀) else 0) := by
      intro i
      exact SCD_point _ _ γ t₀ J hγ ht₀pos (hE i) (le_trans (hA i) hRJ)
    -- level bounds
    have hlevel : ∀ j : ℕ, ∑ i, w i * (if (2 ^ j * t₀ < |fz i (πz i)| ∧
        (∑ k, w k * fz i (πz k) ^ 2) ≤ 2 * (2 ^ j * t₀) / γ) then 2 * (2 ^ j * t₀) else 0)
        ≤ 4 * θ / γ := by
      intro j
      have hδ0 : 0 < 2 ^ j * t₀ := by positivity
      have hδΔ : Δ ≤ 2 ^ j * t₀ := by
        calc Δ ≤ t₀ := hΔt
          _ = 1 * t₀ := (one_mul _).symm
          _ ≤ 2 ^ j * t₀ := mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num)) ht₀pos.le
      have hε2 : 0 ≤ 2 * (2 ^ j * t₀) / γ := by positivity
      have hεγ : γ⁻¹ ≤ Real.sqrt (2 * (2 ^ j * t₀) / γ) := by
        apply Real.le_sqrt_of_sq_le
        have : (γ⁻¹) ^ 2 = γ⁻¹ * γ⁻¹ := sq _
        have h1 : γ⁻¹ ≤ 2 ^ j * t₀ := le_trans hgt (by
          calc t₀ = 1 * t₀ := (one_mul _).symm
            _ ≤ 2 ^ j * t₀ := mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num)) ht₀pos.le)
        have h2 : γ⁻¹ * γ⁻¹ ≤ 2 * (2 ^ j * t₀) / γ := by
          rw [div_eq_mul_inv]
          have : 0 ≤ γ⁻¹ := by positivity
          nlinarith
        rw [this]; exact h2
      have hprob := SCD_prob F R hF w πz hw' Δ γ⁻¹ hΔ (by positivity) (2 ^ j * t₀)
        (Real.sqrt (2 * (2 ^ j * t₀) / γ)) hδΔ hεγ
      rw [Real.sq_sqrt hε2] at hprob
      have hsub : ∑ i, w i * (if (2 ^ j * t₀ < |fz i (πz i)| ∧
          (∑ k, w k * fz i (πz k) ^ 2) ≤ 2 * (2 ^ j * t₀) / γ) then (1:ℝ) else 0) ≤
          distProb w πz (disagreeEvent F (2 ^ j * t₀) (Real.sqrt (2 * (2 ^ j * t₀) / γ)) w πz) := by
        unfold distProb
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (hw0 i)
        split_ifs with h1 h2
        · exact le_refl _
        · exfalso; apply h2
          refine ⟨fz i, hfz i, h1.1, ?_⟩
          rw [Real.sq_sqrt hε2]
          unfold distExp
          exact h1.2
        · norm_num
        · exact le_refl _
      have hcalc : ∑ i, w i * (if (2 ^ j * t₀ < |fz i (πz i)| ∧
          (∑ k, w k * fz i (πz k) ^ 2) ≤ 2 * (2 ^ j * t₀) / γ) then 2 * (2 ^ j * t₀) else 0)
          = 2 * (2 ^ j * t₀) * ∑ i, w i * (if (2 ^ j * t₀ < |fz i (πz i)| ∧
          (∑ k, w k * fz i (πz k) ^ 2) ≤ 2 * (2 ^ j * t₀) / γ) then (1:ℝ) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> ring
      rw [hcalc]
      have hfin : 2 * (2 ^ j * t₀) * (2 * (2 ^ j * t₀) / γ / (2 ^ j * t₀) ^ 2 * θ) = 4 * θ / γ := by
        field_simp
        ring
      calc 2 * (2 ^ j * t₀) * ∑ i, w i * (if (2 ^ j * t₀ < |fz i (πz i)| ∧
          (∑ k, w k * fz i (πz k) ^ 2) ≤ 2 * (2 ^ j * t₀) / γ) then (1:ℝ) else 0)
          ≤ 2 * (2 ^ j * t₀) * (2 * (2 ^ j * t₀) / γ / (2 ^ j * t₀) ^ 2 * θ) :=
            mul_le_mul_of_nonneg_left (le_trans hsub hprob) (by positivity)
        _ = 4 * θ / γ := hfin
    -- assemble
    have hmain : ∑ i, w i * |fz i (πz i)| ≤ t₀ + γ * ∑ i, w i * ∑ j, w j * fz i (πz j) ^ 2 +
        ∑ j ∈ Finset.range J, 4 * θ / γ := by
      calc ∑ i, w i * |fz i (πz i)|
          ≤ ∑ i, w i * (t₀ + γ * (∑ j, w j * fz i (πz j) ^ 2) + ∑ j ∈ Finset.range J,
        (if (2 ^ j * t₀ < |fz i (πz i)| ∧ (∑ k, w k * fz i (πz k) ^ 2) ≤ 2 * (2 ^ j * t₀) / γ)
          then 2 * (2 ^ j * t₀) else 0)) :=
            Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hpt i) (hw0 i))
        _ = t₀ * ∑ i, w i + γ * ∑ i, w i * ∑ j, w j * fz i (πz j) ^ 2 +
            ∑ j ∈ Finset.range J, ∑ i, w i * (if (2 ^ j * t₀ < |fz i (πz i)| ∧
              (∑ k, w k * fz i (πz k) ^ 2) ≤ 2 * (2 ^ j * t₀) / γ) then 2 * (2 ^ j * t₀) else 0) := by
            simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
            rw [Finset.sum_comm (s := Finset.univ) (t := Finset.range J)]
            congr 1
            · congr 1
              · apply Finset.sum_congr rfl; intro i _; ring
              · apply Finset.sum_congr rfl; intro i _; ring
        _ ≤ _ := by
            rw [hw1, mul_one]
            have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range J) => hlevel j)
            linarith
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hmain
    have hθL : (1 + 4 * (J : ℝ)) * θ ≤ 6 * θ * L ^ 2 := by nlinarith
    have hfinal : t₀ + (J : ℝ) * (4 * θ / γ) ≤ 2 * Δ + 6 * θ * L ^ 2 / γ := by
      have h1 : t₀ ≤ Δ + γ⁻¹ := by
        rcases le_total Δ γ⁻¹ with h | h
        · rw [ht₀, max_eq_right h]; linarith
        · rw [ht₀, max_eq_left h]; have : 0 ≤ γ⁻¹ := by positivity
          linarith
      have h2 : γ⁻¹ + (J : ℝ) * (4 * θ / γ) ≤ 6 * θ * L ^ 2 / γ := by
        rw [← sub_nonneg]
        have : 6 * θ * L ^ 2 / γ - (γ⁻¹ + (J : ℝ) * (4 * θ / γ)) =
            (6 * θ * L ^ 2 - (1 + 4 * (J : ℝ) * θ)) / γ := by
          field_simp
        rw [this]
        apply div_nonneg _ hγ.le
        nlinarith
      linarith
    linarith

theorem solution {ι Act : Type*} [Fintype ι] (F : Set (Act → ℝ)) (R : ℝ)
    (hR : 1 ≤ R) (hF : ∀ f ∈ F, ∀ π, |f π| ≤ R) (w : ι → ℝ) (hw : StatComplexityDM.LowerBound.IsDist w)
    (fz : ι → Act → ℝ) (hfz : ∀ i, fz i ∈ F) (πz : ι → Act) (γ : ℝ) (hγ : 0 < γ)
    (Δ : ℝ) (hΔ : 0 < Δ) :
    ∑ i, w i * |fz i (πz i)|
      ≤ 2 * Δ + 6 * disagreementCoeff F Δ γ⁻¹ w πz * Real.log (max (R * γ) (Real.exp 1)) ^ 2 / γ
        + γ * ∑ i, w i * ∑ j, w j * fz i (πz j) ^ 2 :=
  SCD_core F R hR hF w hw fz hfz πz γ hγ Δ hΔ

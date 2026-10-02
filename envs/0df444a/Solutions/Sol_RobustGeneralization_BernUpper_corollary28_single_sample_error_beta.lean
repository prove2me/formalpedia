-- Prove2me | solution 1 for RobustGeneralization.BernUpper.corollary28_single_sample_error_beta
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T07:10:04.09403+00:00
-- url     : https://prove2.me/submissions/62aa2297-d2b5-4f04-9a8f-5a3514a0a9dd

import Mathlib
import Definitions.Def_RobustGeneralization_BernUpper_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory in
theorem ccfc7c7b_hoeff (τ s : ℝ) (h0 : -(1 / 2) ≤ τ) (h1 : τ ≤ 1 / 2) :
    (1 / 2 + τ) * Real.exp (-s) + (1 / 2 - τ) * Real.exp s
      ≤ Real.exp (-2 * τ * s + s ^ 2 / 2) := by
  classical
  set μ : Measure Bool := ENNReal.ofReal (1 / 2 + τ) • Measure.dirac true
    + ENNReal.ofReal (1 / 2 - τ) • Measure.dirac false with hμ
  have hp : IsProbabilityMeasure μ := by
    constructor
    simp only [hμ, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
    norm_num
  have hint : ∀ f : Bool → ℝ, ∫ b, f b ∂μ = (1 / 2 + τ) * f true + (1 / 2 - τ) * f false := by
    intro f
    rw [integral_fintype (Integrable.of_finite), Fintype.sum_bool]
    simp only [hμ, Measure.real, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    simp only [Measure.dirac_apply_of_mem (Set.mem_singleton true),
      Measure.dirac_apply_of_mem (Set.mem_singleton false)]
    simp
    rw [ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
  set X : Bool → ℝ := fun b => (if b then 1 else -1) - 2 * τ with hX
  have hsg := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := μ) (X := X)
    (a := -1 - 2 * τ) (b := 1 - 2 * τ) (Measurable.of_discrete).aemeasurable
    (ae_of_all _ (fun b => by
      cases b <;> simp [hX] <;> constructor <;> linarith))
    (by rw [hint]; simp [hX]; ring)
  have hc : ((‖(1 - 2 * τ) - (-1 - 2 * τ)‖₊ / 2) ^ 2 : NNReal) = 1 := by
    have : (1 - 2 * τ) - (-1 - 2 * τ) = (2 : ℝ) := by ring
    rw [this]
    simp
  have hmgf := hsg.mgf_le (-s)
  rw [hc, mgf, hint] at hmgf
  simp only [hX, if_true, Bool.false_eq_true, if_false, NNReal.coe_one, one_mul] at hmgf
  have e1 : Real.exp (-s) = Real.exp (-2 * τ * s) * Real.exp (-s * (1 - 2 * τ)) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp s = Real.exp (-2 * τ * s) * Real.exp (-s * (-1 - 2 * τ)) := by
    rw [← Real.exp_add]; ring_nf
  have e3 : Real.exp (-2 * τ * s + s ^ 2 / 2) = Real.exp (-2 * τ * s) * Real.exp ((-s) ^ 2 / 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [e1, e2, e3]
  have hpos := Real.exp_pos (-2 * τ * s)
  nlinarith

open RobustGeneralization.BernUpper in
theorem ccfc7c7b_lab_mul_self (b : Bool) : lab b * lab b = 1 := by
  cases b <;> simp [lab]

open RobustGeneralization.BernUpper in
theorem ccfc7c7b_lab_pm (b : Bool) : lab b = 1 ∨ lab b = -1 := by
  cases b <;> simp [lab]

open RobustGeneralization.BernUpper in
theorem ccfc7c7b_inner {d : ℕ} (w x : E d) : inner ℝ w x = ∑ i, w i * x i := by
  simp [PiLp.inner_apply, mul_comm]

open RobustGeneralization.BernUpper in
theorem ccfc7c7b_bernW_nonneg {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1 / 2)
    (p : (Fin d → Bool) × Bool) : 0 ≤ bernW θ τ p := by
  unfold bernW
  apply mul_nonneg (by norm_num)
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith

open RobustGeneralization.BernUpper in
theorem ccfc7c7b_bprob_le {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1 / 2)
    (A : (Fin d → Bool) × Bool → Prop) (f : (Fin d → Bool) × Bool → ℝ)
    (hf : ∀ p, A p → 0 ≤ f p) :
    bprob θ τ A ≤ ∑ p, bernW θ τ p * Real.exp (f p) := by
  unfold bprob
  apply Finset.sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_left _ (ccfc7c7b_bernW_nonneg θ τ h0 h1 p)
  split_ifs with h
  · exact Real.one_le_exp (hf p h)
  · exact (Real.exp_pos _).le

open RobustGeneralization.BernUpper in
theorem ccfc7c7b_mgf {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) (c : Fin d → ℝ) :
    ∑ p : (Fin d → Bool) × Bool, bernW θ τ p * Real.exp (∑ i, c i * (lab p.2 * lab (p.1 i)))
      = ∏ i, ((1 / 2 + τ) * Real.exp (c i * lab (θ i))
          + (1 / 2 - τ) * Real.exp (-(c i * lab (θ i)))) := by
  have key : ∀ y : Bool, ∑ s : Fin d → Bool,
      (∏ i, ((if s i = (y == θ i) then 1 / 2 + τ else 1 / 2 - τ)
        * Real.exp (c i * (lab y * lab (s i)))))
      = ∏ i, ((1 / 2 + τ) * Real.exp (c i * lab (θ i))
          + (1 / 2 - τ) * Real.exp (-(c i * lab (θ i)))) := by
    intro y
    rw [← Fintype.prod_sum (fun i b => (if b = (y == θ i) then 1 / 2 + τ else 1 / 2 - τ)
        * Real.exp (c i * (lab y * lab b)))]
    apply Finset.prod_congr rfl
    intro i _
    rw [Fintype.sum_bool]
    cases y <;> cases h : θ i <;> simp [lab] <;> ring_nf
  have hy : ∀ y : Bool, ∑ s : Fin d → Bool,
      bernW θ τ (s, y) * Real.exp (∑ i, c i * (lab y * lab (s i)))
      = (1 / 2) * ∏ i, ((1 / 2 + τ) * Real.exp (c i * lab (θ i))
          + (1 / 2 - τ) * Real.exp (-(c i * lab (θ i)))) := by
    intro y
    rw [← key y, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    simp only [bernW, Real.exp_sum, Finset.prod_mul_distrib]
    ring
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [Fintype.sum_bool, hy true, hy false]
  ring

open RobustGeneralization.BernUpper in
theorem ccfc7c7b_chernoff {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1 / 2)
    (μ : ℝ) (a c : Fin d → ℝ) (ha : ∀ i, a i = 1 ∨ a i = -1)
    (hc : ∀ i, c i * lab (θ i) = -μ * a i) :
    ∑ p : (Fin d → Bool) × Bool, bernW θ τ p * Real.exp (∑ i, c i * (lab p.2 * lab (p.1 i)))
      ≤ Real.exp (-2 * τ * μ * ∑ i, a i + d * μ ^ 2 / 2) := by
  rw [ccfc7c7b_mgf]
  have hE : Real.exp (-2 * τ * μ * ∑ i, a i + d * μ ^ 2 / 2)
      = ∏ i, Real.exp (-2 * τ * (μ * a i) + (μ * a i) ^ 2 / 2) := by
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    have hsq : ∀ i, (μ * a i) ^ 2 / 2 = μ ^ 2 / 2 := by
      intro i
      rcases ha i with h | h <;> rw [h] <;> ring
    simp only [hsq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      ring
    · ring
  rw [hE]
  apply Finset.prod_le_prod
  · intro i _
    have := Real.exp_pos (c i * lab (θ i))
    have := Real.exp_pos (-(c i * lab (θ i)))
    have h2 : 0 ≤ 1 / 2 - τ := by linarith
    positivity
  · intro i _
    rw [hc i]
    have H := ccfc7c7b_hoeff τ (μ * a i) (by linarith) h1
    have e : -μ * a i = -(μ * a i) := by ring
    rw [e, neg_neg]
    exact H

open RobustGeneralization.BernUpper in
theorem ccfc7c7b_total {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) :
    ∑ p : (Fin d → Bool) × Bool, bernW θ τ p = 1 := by
  have h := ccfc7c7b_mgf θ τ (fun _ => 0)
  have h1 : (1 / 2 + τ) * 1 + (1 / 2 - τ) * 1 = (1 : ℝ) := by ring
  simp only [zero_mul, Finset.sum_const_zero, Real.exp_zero, mul_one, neg_zero] at h
  rw [h]
  have h2 : (1 / 2 + τ) + (1 / 2 - τ) = (1 : ℝ) := by ring
  simp only [h2, Finset.prod_const_one]

open RobustGeneralization.BernUpper in
theorem ccfc7c7b_bprob_le_one {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1 / 2)
    (A : (Fin d → Bool) × Bool → Prop) : bprob θ τ A ≤ 1 := by
  classical
  rw [← ccfc7c7b_total θ τ]
  unfold bprob
  apply Finset.sum_le_sum
  intro p _
  have := ccfc7c7b_bernW_nonneg θ τ h0 h1 p
  split_ifs <;> simp [this]

open RobustGeneralization.BernUpper in
theorem ccfc7c7b_pm_ne {d : ℕ} (hd : 0 < d) (s : Fin d → Bool) : 0 < ‖pm s‖ := by
  rw [norm_pos_iff]
  intro h
  have h0 : (pm s) ⟨0, hd⟩ = 0 := by rw [h]; rfl
  simp only [pm] at h0
  rcases ccfc7c7b_lab_pm (s ⟨0, hd⟩) with h' | h' <;>
    simp [h'] at h0

open RobustGeneralization.BernUpper in
theorem ccfc7c7b_stage2 {d : ℕ} (hd : 0 < d) (θ : Fin d → Bool) (τ : ℝ) (hτ0 : 0 < τ)
    (hτ1 : τ ≤ 1 / 2) (p : (Fin d → Bool) × Bool)
    (hS : τ * d ≤ ∑ i, lab p.2 * lab (p.1 i) * lab (θ i)) :
    clsErr θ τ (linClf (‖pm p.1‖⁻¹ • (lab p.2 • pm p.1))) ≤ Real.exp (-(2 * τ ^ 4 * d)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set S : ℝ := ∑ i, lab p.2 * lab (p.1 i) * lab (θ i) with hSdef
  have hS0 : 0 ≤ S := le_trans (by positivity) hS
  set μ : ℝ := 2 * τ * S / d with hμ
  have hμ0 : 0 ≤ μ := by positivity
  have hcpos : 0 < ‖pm p.1‖⁻¹ := inv_pos.mpr (ccfc7c7b_pm_ne hd p.1)
  calc clsErr θ τ (linClf (‖pm p.1‖⁻¹ • (lab p.2 • pm p.1)))
      ≤ ∑ p' : (Fin d → Bool) × Bool, bernW θ τ p'
          * Real.exp (∑ i, (-μ * (lab p.2 * lab (p.1 i))) * (lab p'.2 * lab (p'.1 i))) := by
        unfold clsErr
        apply ccfc7c7b_bprob_le θ τ hτ0.le hτ1
        intro p' hne
        have hin : inner ℝ (‖pm p.1‖⁻¹ • (lab p.2 • pm p.1)) (pm p'.1)
            = ‖pm p.1‖⁻¹ * ∑ i, lab p.2 * lab (p.1 i) * lab (p'.1 i) := by
          rw [real_inner_smul_left, ccfc7c7b_inner]
          congr 1
        have hsum : ∑ i, (-μ * (lab p.2 * lab (p.1 i))) * (lab p'.2 * lab (p'.1 i))
            = -μ * (lab p'.2 * ∑ i, lab p.2 * lab (p.1 i) * lab (p'.1 i)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [hsum]
        simp only [linClf, hin] at hne
        set I : ℝ := ∑ i, lab p.2 * lab (p.1 i) * lab (p'.1 i) with hI
        have hI' : (0 ≤ ‖pm p.1‖⁻¹ * I) ↔ 0 ≤ I := by
          constructor
          · intro h; by_contra h'; push_neg at h'; nlinarith
          · intro h; positivity
        cases hy : p'.2 <;> rw [hy] at hne <;> simp [lab, hI'] at hne ⊢ <;> nlinarith
    _ ≤ Real.exp (-2 * τ * μ * S + d * μ ^ 2 / 2) :=
        ccfc7c7b_chernoff θ τ hτ0.le hτ1 μ
          (fun i => lab p.2 * lab (p.1 i) * lab (θ i))
          (fun i => -μ * (lab p.2 * lab (p.1 i)))
          (fun i => by
            rcases ccfc7c7b_lab_pm p.2 with h1 | h1 <;>
            rcases ccfc7c7b_lab_pm (p.1 i) with h2 | h2 <;>
            rcases ccfc7c7b_lab_pm (θ i) with h3 | h3 <;>
            simp [h1, h2, h3])
          (fun i => by ring)
    _ ≤ Real.exp (-(2 * τ ^ 4 * d)) := by
        apply Real.exp_le_exp.mpr
        have e : -2 * τ * μ * S + d * μ ^ 2 / 2 = -(2 * τ ^ 2 * S ^ 2 / d) := by
          rw [hμ]; field_simp; ring
        rw [e, neg_le_neg_iff, le_div_iff₀ hdpos]
        have hsq : (τ * d) ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ (by positivity) hS 2
        have hτ2 : 0 ≤ 2 * τ ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hsq hτ2]

open RobustGeneralization.BernUpper in
theorem solution {d : ℕ} (θ : Fin d → Bool) (τ : ℝ)
    (hτ : 0 < τ) (hτ' : τ ≤ 1 / 2) (β : ℝ) (hβ : 0 < β)
    (hτβ : (Real.log (1 / β) / (2 * d)) ^ ((1 : ℝ) / 4) ≤ τ) :
    bprob θ τ (fun p => β < clsErr θ τ (linClf (‖pm p.1‖⁻¹ • (lab p.2 • pm p.1))))
      ≤ Real.exp (-(τ ^ 2 * d / 2)) := by
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · subst hd0
    simp only [Nat.cast_zero, mul_zero, zero_div, neg_zero, Real.exp_zero]
    exact ccfc7c7b_bprob_le_one θ τ hτ.le hτ' _
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  by_cases hβ1 : 1 ≤ β
  · have : bprob θ τ (fun p => β < clsErr θ τ (linClf (‖pm p.1‖⁻¹ • (lab p.2 • pm p.1)))) = 0 := by
      unfold bprob
      apply Finset.sum_eq_zero
      intro p _
      rw [if_neg]
      · ring
      · push_neg
        exact le_trans (ccfc7c7b_bprob_le_one θ τ hτ.le hτ' _) hβ1
    rw [this]
    exact (Real.exp_pos _).le
  push_neg at hβ1
  -- exp(-2 τ^4 d) ≤ β
  have hkey : Real.exp (-(2 * τ ^ 4 * d)) ≤ β := by
    have hlog : 0 < Real.log (1 / β) := Real.log_pos (by rw [one_div, one_lt_inv₀ hβ]; exact hβ1)
    set L : ℝ := Real.log (1 / β) / (2 * d) with hL
    have hLpos : 0 < L := by positivity
    have hL4 : (L ^ ((1 : ℝ) / 4)) ^ 4 = L := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
      norm_num
    have hLτ : L ≤ τ ^ 4 := by
      rw [← hL4]
      exact pow_le_pow_left₀ (Real.rpow_nonneg hLpos.le _) hτβ 4
    have h2 : Real.log (1 / β) ≤ 2 * τ ^ 4 * d := by
      rw [hL, div_le_iff₀ (by positivity)] at hLτ
      linarith
    rw [one_div, Real.log_inv] at h2
    calc Real.exp (-(2 * τ ^ 4 * d)) ≤ Real.exp (Real.log β) := Real.exp_le_exp.mpr (by linarith)
      _ = β := Real.exp_log hβ
  have hsumeq : ∀ p : (Fin d → Bool) × Bool,
      ∑ i, (-τ * lab (θ i)) * (lab p.2 * lab (p.1 i))
        = -τ * ∑ i, lab p.2 * lab (p.1 i) * lab (θ i) := by
    intro p
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  calc bprob θ τ (fun p => β < clsErr θ τ (linClf (‖pm p.1‖⁻¹ • (lab p.2 • pm p.1))))
      ≤ ∑ p : (Fin d → Bool) × Bool, bernW θ τ p
          * Real.exp (τ * (τ * d) + ∑ i, (-τ * lab (θ i)) * (lab p.2 * lab (p.1 i))) := by
        apply ccfc7c7b_bprob_le θ τ hτ.le hτ'
        intro p hbad
        have hS : ∑ i, lab p.2 * lab (p.1 i) * lab (θ i) ≤ τ * d := by
          by_contra hS
          have := ccfc7c7b_stage2 hd θ τ hτ hτ' p (not_le.mp hS).le
          linarith
        rw [hsumeq p]
        nlinarith
    _ = Real.exp (τ * (τ * d)) * ∑ p : (Fin d → Bool) × Bool, bernW θ τ p
          * Real.exp (∑ i, (-τ * lab (θ i)) * (lab p.2 * lab (p.1 i))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        rw [Real.exp_add]
        ring
    _ ≤ Real.exp (τ * (τ * d)) * Real.exp (-2 * τ * τ * ∑ _i : Fin d, (1 : ℝ) + d * τ ^ 2 / 2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact ccfc7c7b_chernoff θ τ hτ.le hτ' τ (fun _ => 1) (fun i => -τ * lab (θ i))
          (fun _ => Or.inl rfl)
          (fun i => by rw [mul_assoc, ccfc7c7b_lab_mul_self])
    _ = Real.exp (-(τ ^ 2 * d / 2)) := by
        rw [← Real.exp_add]
        congr 1
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        ring

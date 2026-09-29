-- Prove2me | solution 1 for RobustGeneralization.BernUpper.lemma26_fixed_direction_tail
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:27:17.572948+00:00
-- url     : https://prove2.me/submissions/f2227694-d349-4450-becb-622ae5b41130

import Mathlib
import Definitions.Def_RobustGeneralization_BernUpper_Model

namespace RobustGeneralization.BernUpper

open MeasureTheory ProbabilityTheory

theorem aux_l26_hoeff (q c t : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    q * Real.exp (t * c) + (1 - q) * Real.exp (-(t * c))
      ≤ Real.exp (t * ((2 * q - 1) * c) + t ^ 2 * c ^ 2 / 2) := by
  let μ : Measure Bool := ENNReal.ofReal q • Measure.dirac true
    + ENNReal.ofReal (1 - q) • Measure.dirac false
  have hμt : μ.real {true} = q := by
    simp [μ, Measure.real, hq0]
  have hμf : μ.real {false} = 1 - q := by
    simp [μ, Measure.real, hq1]
  have : IsProbabilityMeasure μ := by
    constructor
    simp only [μ, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hq0 (by linarith)]
    simp
  let X : Bool → ℝ := fun b => if b then c else -c
  have hX : AEMeasurable X μ := (measurable_of_finite X).aemeasurable
  have hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (-|c|) |c| := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    cases ω <;> simp [X, neg_abs_le, le_abs_self, neg_le_abs]
  have hsub := hasSubgaussianMGF_of_mem_Icc hX hb
  have hmean : μ[X] = (2 * q - 1) * c := by
    rw [integral_fintype (Integrable.of_finite)]
    simp [hμt, hμf, X]
    ring
  have hm := hsub.mgf_le t
  rw [hmean] at hm
  have hmgf : mgf (fun ω => X ω - (2 * q - 1) * c) μ t
      = q * Real.exp (t * (c - (2 * q - 1) * c)) + (1 - q) * Real.exp (t * (-c - (2 * q - 1) * c)) := by
    rw [mgf, integral_fintype (Integrable.of_finite)]
    simp [hμt, hμf, X]
  have hcoef : (((‖|c| - -|c|‖₊ / 2) ^ 2 : NNReal) : ℝ) = c ^ 2 := by
    simp
    rw [abs_of_nonneg (by positivity), show (|c| + |c|) / 2 = |c| by ring, sq_abs]
  rw [hmgf, hcoef] at hm
  have e1 : Real.exp (t * c) = Real.exp (t * ((2 * q - 1) * c)) * Real.exp (t * (c - (2 * q - 1) * c)) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-(t * c)) = Real.exp (t * ((2 * q - 1) * c)) * Real.exp (t * (-c - (2 * q - 1) * c)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e1, e2, Real.exp_add]
  have hpos := Real.exp_pos (t * ((2 * q - 1) * c))
  calc q * (Real.exp (t * ((2 * q - 1) * c)) * Real.exp (t * (c - (2 * q - 1) * c))) +
        (1 - q) * (Real.exp (t * ((2 * q - 1) * c)) * Real.exp (t * (-c - (2 * q - 1) * c)))
      = Real.exp (t * ((2 * q - 1) * c)) * (q * Real.exp (t * (c - (2 * q - 1) * c)) +
          (1 - q) * Real.exp (t * (-c - (2 * q - 1) * c))) := by ring
    _ ≤ Real.exp (t * ((2 * q - 1) * c)) * Real.exp (c ^ 2 * t ^ 2 / 2) := by gcongr
    _ = _ := by ring_nf


theorem aux_l26_inner_pm {d : ℕ} (w : E d) (θ : Fin d → Bool) :
    inner ℝ w (pm θ) = ∑ i, w i * lab (θ i) := by
  simp [pm, PiLp.inner_apply, mul_comm]

theorem aux_l26_inner_z {d : ℕ} (w : E d) (p : (Fin d → Bool) × Bool) :
    inner ℝ w (zvec p) = ∑ i, w i * (lab p.2 * lab (p.1 i)) := by
  simp [zvec, pm, PiLp.inner_apply, mul_comm]

theorem aux_l26_normsq {d : ℕ} (w : E d) (hw : ‖w‖ = 1) :
    ∑ i, w i ^ 2 = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at hw
  simpa [Real.norm_eq_abs, sq_abs] using hw



theorem aux_l26_mgf {d : ℕ} (θ : Fin d → Bool) (τ l : ℝ) (w : E d) :
    ∑ p, bernW θ τ p * Real.exp (-(l * ∑ i, w i * (lab p.2 * lab (p.1 i))))
      = ∏ i, ((1 / 2 + τ) * Real.exp (-(l * (w i * lab (θ i))))
          + (1 / 2 - τ) * Real.exp (l * (w i * lab (θ i)))) := by
  classical
  set G : Fin d → ℝ := fun i => (1 / 2 + τ) * Real.exp (-(l * (w i * lab (θ i))))
          + (1 / 2 - τ) * Real.exp (l * (w i * lab (θ i))) with hG
  let h : Bool → Fin d → Bool → ℝ := fun y i b =>
    (if b = (y == θ i) then 1 / 2 + τ else 1 / 2 - τ) * Real.exp (-(l * (w i * (lab y * lab b))))
  have hterm : ∀ (y : Bool) (s : Fin d → Bool),
      bernW θ τ (s, y) * Real.exp (-(l * ∑ i, w i * (lab y * lab (s i))))
        = (1 / 2) * ∏ i, h y i (s i) := by
    intro y s
    simp only [bernW, h]
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum, mul_assoc,
      ← Finset.prod_mul_distrib]
  have hsumb : ∀ (y : Bool) (i : Fin d), ∑ b, h y i b = G i := by
    intro y i
    rw [Fintype.sum_bool]
    simp only [h, hG]
    cases y <;> cases θ i <;> simp [lab] <;> ring_nf
  have hy : ∀ y : Bool, ∑ s : Fin d → Bool,
      bernW θ τ (s, y) * Real.exp (-(l * ∑ i, w i * (lab y * lab (s i)))) = (1 / 2) * ∏ i, G i := by
    intro y
    simp_rw [hterm y]
    rw [← Finset.mul_sum, ← Fintype.prod_sum]
    simp_rw [hsumb y]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only
  simp_rw [hy]
  rw [Fintype.sum_bool]
  ring


theorem aux_l26_bernW_nonneg {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) (hτ : 0 < τ) (hτ' : τ ≤ 1 / 2)
    (p : (Fin d → Bool) × Bool) : 0 ≤ bernW θ τ p := by
  unfold bernW
  apply mul_nonneg (by norm_num)
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith

theorem aux_l26_lab_sq (b : Bool) : lab b ^ 2 = 1 := by
  cases b <;> simp [lab]

end RobustGeneralization.BernUpper

open RobustGeneralization.BernUpper

theorem solution {d : ℕ} (θ : Fin d → Bool) (τ : ℝ)
    (hτ : 0 < τ) (hτ' : τ ≤ 1 / 2) (w : E d) (hw : ‖w‖ = 1)
    (hwθ : 0 ≤ inner ℝ w ((2 * τ) • pm θ)) :
    bprob θ τ (fun p => inner ℝ w (zvec p) ≤ 0)
      ≤ Real.exp (-(2 * τ ^ 2 * (inner ℝ w (pm θ)) ^ 2)) := by
  obtain ⟨m, hm_def⟩ : ∃ m, inner ℝ w (pm θ) = m := ⟨_, rfl⟩
  have hmS : ∑ i, w i * lab (θ i) = m := by rw [← aux_l26_inner_pm, hm_def]
  rw [inner_smul_right, hm_def] at hwθ
  rw [hm_def]
  have hm0 : 0 ≤ m := by
    by_contra hneg
    rw [not_le] at hneg
    have : 2 * τ * m < 0 := mul_neg_of_pos_of_neg (by linarith) hneg
    linarith
  obtain ⟨l, hl⟩ : ∃ l, 2 * τ * m = l := ⟨_, rfl⟩
  have hl0 : 0 ≤ l := by rw [← hl]; positivity
  have step1 : bprob θ τ (fun p => inner ℝ w (zvec p) ≤ 0)
      ≤ ∑ p, bernW θ τ p * Real.exp (-(l * ∑ i, w i * (lab p.2 * lab (p.1 i)))) := by
    unfold bprob
    apply Finset.sum_le_sum
    intro p _
    apply mul_le_mul_of_nonneg_left _ (aux_l26_bernW_nonneg θ τ hτ hτ' p)
    rw [← aux_l26_inner_z]
    split_ifs with hA
    · apply Real.one_le_exp
      nlinarith
    · exact (Real.exp_pos _).le
  rw [aux_l26_mgf] at step1
  refine step1.trans ?_
  have hG : ∀ i, (1 / 2 + τ) * Real.exp (-(l * (w i * lab (θ i))))
      + (1 / 2 - τ) * Real.exp (l * (w i * lab (θ i)))
      ≤ Real.exp ((-l) * ((2 * (1 / 2 + τ) - 1) * (w i * lab (θ i)))
          + (-l) ^ 2 * (w i * lab (θ i)) ^ 2 / 2) := by
    intro i
    have := aux_l26_hoeff (1 / 2 + τ) (w i * lab (θ i)) (-l) (by linarith) (by linarith)
    rw [neg_mul, neg_neg] at this
    convert this using 2
    ring
  calc ∏ i, ((1 / 2 + τ) * Real.exp (-(l * (w i * lab (θ i))))
          + (1 / 2 - τ) * Real.exp (l * (w i * lab (θ i))))
      ≤ ∏ i, Real.exp ((-l) * ((2 * (1 / 2 + τ) - 1) * (w i * lab (θ i)))
          + (-l) ^ 2 * (w i * lab (θ i)) ^ 2 / 2) := by
        apply Finset.prod_le_prod
        · intro i _
          have h1 : 0 ≤ 1 / 2 - τ := by linarith
          positivity
        · intro i _
          exact hG i
    _ = Real.exp (∑ i, ((-l) * ((2 * (1 / 2 + τ) - 1) * (w i * lab (θ i)))
          + (-l) ^ 2 * (w i * lab (θ i)) ^ 2 / 2)) := (Real.exp_sum _ _).symm
    _ = Real.exp (-(2 * τ ^ 2 * m ^ 2)) := by
        congr 1
        have hsum : ∑ i, ((-l) * ((2 * (1 / 2 + τ) - 1) * (w i * lab (θ i)))
            + (-l) ^ 2 * (w i * lab (θ i)) ^ 2 / 2)
            = -(2 * l * τ) * (∑ i, w i * lab (θ i)) + l ^ 2 / 2 * ∑ i, w i ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          have := aux_l26_lab_sq (θ i)
          linear_combination (l ^ 2 / 2 * w i ^ 2) * this
        rw [hsum, hmS, aux_l26_normsq w hw, ← hl]
        ring

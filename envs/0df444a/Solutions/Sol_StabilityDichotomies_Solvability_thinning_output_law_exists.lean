-- Prove2me | solution 1 for StabilityDichotomies.Solvability.thinning_output_law_exists
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:58:09.900419+00:00
-- url     : https://prove2.me/submissions/c4b1e55b-210d-4a60-9fd8-4709d3c392cc

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory StabilityDichotomies.Solvability

private theorem bernoulli_weights_sum (m : ℕ) (p : ℝ) :
    (∑ mask : Fin m → Bool, retentionWeight p mask) = 1 := by
  unfold retentionWeight
  have h := (Fintype.prod_sum (fun _ : Fin m => fun b : Bool => if b then p else 1 - p)).symm
  simpa using h


private def q {X : Type} [Fintype X] (m : ℕ) (out : (Fin m → Bool) → X) (ε : ℝ) (x : X) : ℝ :=
  ε⁻¹ * ∫ p in (1-ε)..1, ∑ mask : Fin m → Bool,
    retentionWeight p mask * (if out mask = x then 1 else 0)

private theorem q_nonneg {X : Type} [Fintype X] (m : ℕ) (out : (Fin m → Bool) → X)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (x : X) : 0 ≤ q m out ε x := by
  unfold q
  apply mul_nonneg (inv_nonneg.mpr (le_of_lt hε))
  apply intervalIntegral.integral_nonneg (by linarith)
  intro p hp
  have hp0 : 0 ≤ p := by linarith [hp.1]
  have hp1 : p ≤ 1 := hp.2
  apply Finset.sum_nonneg
  intro mask hm
  apply mul_nonneg
  · unfold retentionWeight
    apply Finset.prod_nonneg
    intro j hj
    split_ifs <;> linarith
  · split_ifs <;> norm_num

private theorem q_sum {X : Type} [Fintype X] (m : ℕ) (out : (Fin m → Bool) → X)
    (ε : ℝ) (hε : 0 < ε) : (∑ x : X, q m out ε x) = 1 := by
  have hc (mask : Fin m → Bool) : Continuous (fun p : ℝ => retentionWeight p mask) := by
    unfold retentionWeight
    apply continuous_finsetProd
    intro j hj
    cases hm : mask j <;> simp only [hm, Bool.false_eq_true, ↓reduceIte]
    · exact continuous_const.sub continuous_id
    · exact continuous_id
  have hcont (x : X) : Continuous (fun p : ℝ => ∑ mask : Fin m → Bool,
      retentionWeight p mask * (if out mask = x then 1 else 0)) := by fun_prop
  unfold q
  rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum (fun x hx => (hcont x).intervalIntegrable _ _)]
  have hs (p : ℝ) : (∑ x : X, ∑ mask : Fin m → Bool,
      retentionWeight p mask * (if out mask = x then 1 else 0)) = 1 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp [bernoulli_weights_sum]
  simp_rw [hs]
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_sub_cancel]
  exact inv_mul_cancel₀ (ne_of_gt hε)

theorem solution (Γ : Language) (b : Bool) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) : ∃ A : Solver Γ, ThinningOutputLaw Γ b ε A := by
  let A : Solver Γ := fun V _ I =>
    PMF.ofFintype (fun x => ENNReal.ofReal (q I.constraints.card
      (fun mask => extremalSolution (thinnedInstance I mask) b) ε x)) (by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun x hx => q_nonneg _ _ ε hε hε1 x)]
        rw [q_sum _ _ ε hε, ENNReal.ofReal_one])
  refine ⟨A, ?_⟩
  intro V _ I hI x
  change ((PMF.ofFintype _ _) x).toReal = _
  simp only [PMF.ofFintype_apply, ENNReal.toReal_ofReal (q_nonneg _ _ ε hε hε1 x)]
  simp [q]

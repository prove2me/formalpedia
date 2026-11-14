-- Prove2me | solution 1 for StabilityDichotomies.Solvability.shared_seed_for_uniform_bernoulli_mixture
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:10:25.924404+00:00
-- url     : https://prove2.me/submissions/ce9825b5-26a6-4118-9f23-b0329862a4e8

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

private theorem q_identity (m : ℕ) (ε : ℝ) (mask : Fin m → Bool) :
    q m id ε mask = ε⁻¹ * ∫ p in (1-ε)..1, retentionWeight p mask := by
  unfold q
  congr 2
  funext p
  simp

private theorem q_reindex {X : Type} [Fintype X] (m : ℕ) (f : (Fin m → Bool) → X)
    (ε : ℝ) (x : X) :
    (∑ mask : Fin m → Bool, if x = f mask then q m id ε mask else 0) = q m f ε x := by
  have hc (mask : Fin m → Bool) : Continuous (fun p : ℝ => retentionWeight p mask) := by
    unfold retentionWeight
    apply continuous_finsetProd
    intro j hj
    cases hm : mask j <;> simp only [hm, Bool.false_eq_true, ↓reduceIte]
    · exact continuous_const.sub continuous_id
    · exact continuous_id
  have he (mask : Fin m → Bool) :
      (if x = f mask then q m id ε mask else 0) = ε⁻¹ *
        ∫ p in (1-ε)..1, retentionWeight p mask * (if f mask = x then 1 else 0) := by
    by_cases hh : x = f mask
    · simp [hh, q_identity]
    · have hh' : f mask ≠ x := Ne.symm hh
      simp [hh,hh']
  simp_rw [he]
  rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum]
  · rfl
  · intro mask hm
    have : Continuous (fun p : ℝ => retentionWeight p mask * (if f mask = x then 1 else 0)) := by fun_prop
    exact this.intervalIntegrable _ _

theorem solution (m : ℕ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ ρ : PMF (Fin m → Bool), ∀ (X : Type) [Fintype X]
      (f : (Fin m → Bool) → X) (x : X),
      ((ρ.map f) x).toReal = ε⁻¹ * ∫ p in (1-ε)..1,
        ∑ mask : Fin m → Bool, retentionWeight p mask * (if f mask = x then 1 else 0) := by
  let ρ : PMF (Fin m → Bool) := PMF.ofFintype (fun mask => ENNReal.ofReal (q m id ε mask)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun mask hm => q_nonneg m id ε hε hε1 mask)]
    rw [q_sum m id ε hε, ENNReal.ofReal_one])
  refine ⟨ρ, ?_⟩
  intro X _ f x
  rw [PMF.map_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (by intro z hz; split_ifs <;> simp [PMF.apply_ne_top])]
  simp only [apply_ite, ENNReal.toReal_zero]
  have hr (mask : Fin m → Bool) : (ρ mask).toReal = q m id ε mask := by
    change ((PMF.ofFintype _ _) mask).toReal = _
    simp [ENNReal.toReal_ofReal (q_nonneg m id ε hε hε1 mask)]
  simp_rw [hr]
  simpa [q] using q_reindex m f ε x

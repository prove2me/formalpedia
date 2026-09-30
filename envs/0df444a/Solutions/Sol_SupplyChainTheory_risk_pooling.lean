-- Prove2me | solution 1 for SupplyChainTheory.risk_pooling
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T04:48:06.331639+00:00
-- url     : https://prove2.me/submissions/ab893e07-639f-4824-9bcc-e51c76887b5b

import Mathlib
import Definitions.Def_SupplyChainTheory_flexibility

open MeasureTheory ProbabilityTheory

namespace SupplyChainTheory

section RiskPooling

lemma rp_nonneg (h p : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) (D : Measure ℝ) (S : ℝ) :
    0 ≤ ∫ d, (h * max (S - d) 0 + p * max (d - S) 0) ∂D :=
  integral_nonneg fun _ =>
    add_nonneg (mul_nonneg hh (le_max_right _ _)) (mul_nonneg hp (le_max_right _ _))

lemma rp_bdd (h p : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) (D : Measure ℝ) :
    BddBelow (Set.range (fun S : ℝ => ∫ d, (h * max (S - d) 0 + p * max (d - S) 0) ∂D)) :=
  ⟨0, by rintro _ ⟨S, rfl⟩; exact rp_nonneg h p hh hp D S⟩

lemma rp_cost_nonneg (h p : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) (D : Measure ℝ) :
    0 ≤ optNvCost h p D := by
  unfold optNvCost
  exact Real.sInf_nonneg (by rintro _ ⟨S, rfl⟩; exact rp_nonneg h p hh hp D S)

/-- `N(m, v)` is the image of the standard normal law under `z ↦ √v z + m`. -/
lemma rp_map (m : ℝ) (v : NNReal) :
    (gaussianReal 0 1).map (fun z => Real.sqrt v * z + m) = gaussianReal m v := by
  have h1 : ((gaussianReal 0 1).map (fun x : ℝ => Real.sqrt v * x)).map (fun x : ℝ => x + m)
      = (gaussianReal 0 1).map (fun z => Real.sqrt v * z + m) :=
    Measure.map_map (by fun_prop) (by fun_prop)
  rw [← h1, gaussianReal_map_const_mul, gaussianReal_map_add_const]
  congr 1
  · ring
  · ext
    simp [Real.sq_sqrt (NNReal.coe_nonneg v)]

/-- Scaling: the cost at level `m + √v t` under `N(m, v)` is `√v` times the standard cost at
level `t`. -/
lemma rp_scale (h p m : ℝ) (v : NNReal) (t : ℝ) :
    ∫ d, (h * max ((m + Real.sqrt v * t) - d) 0 + p * max (d - (m + Real.sqrt v * t)) 0)
        ∂(gaussianReal m v)
      = Real.sqrt v * ∫ z, (h * max (t - z) 0 + p * max (z - t) 0) ∂(gaussianReal 0 1) := by
  have hσ : 0 ≤ Real.sqrt v := Real.sqrt_nonneg _
  rw [← rp_map m v, integral_map (by fun_prop) (Continuous.aestronglyMeasurable (by fun_prop)),
    ← integral_const_mul]
  congr 1
  funext z
  have e1 : m + Real.sqrt v * t - (Real.sqrt v * z + m) = Real.sqrt v * (t - z) := by ring
  have e2 : Real.sqrt v * z + m - (m + Real.sqrt v * t) = Real.sqrt v * (z - t) := by ring
  have hm : ∀ a : ℝ, max (Real.sqrt v * a) 0 = Real.sqrt v * max a 0 := fun a => by
    rw [mul_max_of_nonneg _ _ hσ, mul_zero]
  rw [e1, e2, hm, hm]
  ring

lemma rp_upper (h p : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) (m : ℝ) (v : NNReal) :
    optNvCost h p (gaussianReal m v) ≤ Real.sqrt v * optNvCost h p (gaussianReal 0 1) := by
  have hσ : 0 ≤ Real.sqrt v := Real.sqrt_nonneg _
  change sInf _ ≤ Real.sqrt v * ⨅ t : ℝ, _
  rw [Real.mul_iInf_of_nonneg hσ]
  refine le_ciInf fun t => ?_
  rw [← rp_scale h p m v t]
  exact csInf_le (rp_bdd h p hh hp _) ⟨m + Real.sqrt v * t, rfl⟩

lemma rp_lower (h p : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) (m : ℝ) (v : NNReal) (hv : 0 < (v : ℝ)) :
    Real.sqrt v * optNvCost h p (gaussianReal 0 1) ≤ optNvCost h p (gaussianReal m v) := by
  have hσ : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  unfold optNvCost
  refine le_csInf (Set.range_nonempty _) ?_
  rintro _ ⟨S, rfl⟩
  have e : m + Real.sqrt v * ((S - m) / Real.sqrt v) = S := by
    field_simp
    ring
  have hs := rp_scale h p m v ((S - m) / Real.sqrt v)
  rw [e] at hs
  simp only
  rw [hs]
  exact mul_le_mul_of_nonneg_left
    (csInf_le (rp_bdd h p hh hp _) ⟨(S - m) / Real.sqrt v, rfl⟩) hσ.le

lemma rp_pooled_le {N : ℕ} (sig : Fin N → ℝ) (rho : Fin N → Fin N → ℝ)
    (hsig : ∀ i, 0 < sig i) (hrho : ∀ i j, rho i j ≤ 1) :
    Real.sqrt (Real.toNNReal (pooledVariance sig rho)) ≤ ∑ i, sig i := by
  have hs : 0 ≤ ∑ i, sig i := Finset.sum_nonneg fun i _ => (hsig i).le
  have hpv : pooledVariance sig rho ≤ (∑ i, sig i) ^ 2 := by
    unfold pooledVariance
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    exact mul_le_of_le_one_right (mul_nonneg (hsig i).le (hsig j).le) (hrho i j)
  rw [Real.coe_toNNReal']
  calc Real.sqrt (max (pooledVariance sig rho) 0) ≤ Real.sqrt ((∑ i, sig i) ^ 2) :=
        Real.sqrt_le_sqrt (max_le hpv (sq_nonneg _))
    _ = ∑ i, sig i := Real.sqrt_sq hs

theorem rp_main {N : ℕ} (h p : ℝ) (hh : 0 < h) (hp : 0 < p)
    (mu sig : Fin N → ℝ) (rho : Fin N → Fin N → ℝ)
    (hsig : ∀ i, 0 < sig i) (hrho : ∀ i j, rho i j ≤ 1) :
    optNvCost h p (gaussianReal (∑ i, mu i) (Real.toNNReal (pooledVariance sig rho)))
      ≤ ∑ i, optNvCost h p (gaussianReal (mu i) (Real.toNNReal ((sig i) ^ 2))) := by
  have hc0 : 0 ≤ optNvCost h p (gaussianReal 0 1) := rp_cost_nonneg h p hh.le hp.le _
  calc optNvCost h p (gaussianReal (∑ i, mu i) (Real.toNNReal (pooledVariance sig rho)))
      ≤ Real.sqrt (Real.toNNReal (pooledVariance sig rho)) * optNvCost h p (gaussianReal 0 1) :=
        rp_upper h p hh.le hp.le _ _
    _ ≤ (∑ i, sig i) * optNvCost h p (gaussianReal 0 1) :=
        mul_le_mul_of_nonneg_right (rp_pooled_le sig rho hsig hrho) hc0
    _ = ∑ i, sig i * optNvCost h p (gaussianReal 0 1) := Finset.sum_mul _ _ _
    _ ≤ ∑ i, optNvCost h p (gaussianReal (mu i) (Real.toNNReal ((sig i) ^ 2))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hv : ((Real.toNNReal ((sig i) ^ 2) : NNReal) : ℝ) = (sig i) ^ 2 :=
          Real.coe_toNNReal _ (sq_nonneg _)
        have hsq : Real.sqrt ((Real.toNNReal ((sig i) ^ 2) : NNReal) : ℝ) = sig i := by
          rw [hv, Real.sqrt_sq (hsig i).le]
        have := rp_lower h p hh.le hp.le (mu i) (Real.toNNReal ((sig i) ^ 2))
          (by rw [hv]; exact pow_pos (hsig i) 2)
        rwa [hsq] at this

end RiskPooling

end SupplyChainTheory

open SupplyChainTheory

theorem solution {N : ℕ} (h p : ℝ) (hh : 0 < h) (hp : 0 < p)
    (mu sig : Fin N → ℝ) (rho : Fin N → Fin N → ℝ)
    (hsig : ∀ i, 0 < sig i) (hrho : ∀ i j, rho i j ≤ 1) (hrho_diag : ∀ i, rho i i = 1)
    (hrho_symm : ∀ i j, rho i j = rho j i) :
    optNvCost h p
        (ProbabilityTheory.gaussianReal (∑ i, mu i) (Real.toNNReal (pooledVariance sig rho)))
      ≤ ∑ i, optNvCost h p
          (ProbabilityTheory.gaussianReal (mu i) (Real.toNNReal ((sig i) ^ 2))) := by
  exact rp_main h p hh hp mu sig rho hsig hrho

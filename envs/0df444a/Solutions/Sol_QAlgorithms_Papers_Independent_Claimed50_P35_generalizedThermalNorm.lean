-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P35.generalizedThermalNorm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:55:07.567804+00:00
-- url     : https://prove2.me/submissions/b17bf217-6c9f-42b3-99d2-2d5a6cb208ee

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35
noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50 QAlgorithms.Papers.Independent.Claimed50.P35

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39
  (displacementMatrix attenuatorMatrix amplifierMatrix thermalMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation conjugateKernel composeKernel partialRight isometryCoeff identityCoeff)

open QAlgorithms.Papers.Independent.Frontier30.P21 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

section G68ILIB
open Filter MeasureTheory
open scoped Topology ENNReal NNReal BigOperators
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33

lemma g68i_cs_lp (a b : Hilbert ℕ) (s : Finset ℕ) :
    ∑ i ∈ s, ‖a i‖ * ‖b i‖ ≤ ‖a‖ * ‖b‖ := by
  have h2 : ∀ f : Hilbert ℕ, Real.sqrt (∑ i ∈ s, ‖f i‖ ^ 2) ≤ ‖f‖ := by
    intro f
    have := lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) f s
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at this
    rw [Real.sqrt_le_left]
    · exact this
    · exact norm_nonneg _
  exact (Real.sum_mul_le_sqrt_mul_sqrt s _ _).trans
    (mul_le_mul (h2 a) (h2 b) (Real.sqrt_nonneg _) (norm_nonneg _))

lemma g68i_smul_apply (c : ℂ) (v : Hilbert ℕ) (k : ℕ) : (c • v) k = c * v k := rfl

lemma g68i_diag_ts (d : ℕ → ℝ) (hs : Summable (fun n => |d n|)) (X : Matrix ℕ ℕ ℂ)
    (hX : ∀ i j, X i j = if i = j then (d i : ℂ) else 0) :
    IsTraceClass X ∧ traceSize X = ENNReal.ofReal (∑' n, |d n|) := by
  let e : NuclearExpansion X :=
    { left := fun n => (d n : ℂ) • lp.single 2 n (1 : ℂ)
      right := fun n => lp.single 2 n (1 : ℂ)
      summable := by
        refine hs.congr (fun n => ?_)
        rw [norm_smul, lp.norm_single (p := 2) (by norm_num)]
        simp
      coefficients := by
        intro i j
        simp only [g68i_smul_apply]
        rw [hX, tsum_eq_single i]
        · by_cases hij : i = j
          · subst hij; simp [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply, Pi.single_apply]
          · simp [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply, Pi.single_apply, hij, Ne.symm hij]
        · intro n hn
          simp [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply, Pi.single_apply, Ne.symm hn] }
  refine ⟨⟨e⟩, le_antisymm ?_ ?_⟩
  · refine iInf_le_of_le e (le_of_eq ?_)
    congr 1
    refine tsum_congr (fun n => ?_)
    simp only [e]
    rw [norm_smul, lp.norm_single (p := 2) (by norm_num)]
    simp
  · refine le_iInf (fun f => ENNReal.ofReal_le_ofReal ?_)
    refine Real.tsum_le_of_sum_le (fun n => abs_nonneg _) (fun s => ?_)
    have hb : ∀ i, |d i| ≤ ∑' n, ‖f.left n i‖ * ‖f.right n i‖ := by
      intro i
      have hc := f.coefficients i i
      rw [hX, if_pos rfl] at hc
      have hb1 : ∀ n, ‖f.left n i * star (f.right n i)‖ ≤ ‖f.left n‖ * ‖f.right n‖ := by
        intro n
        rw [norm_mul, norm_star]
        exact mul_le_mul (lp.norm_apply_le_norm two_ne_zero _ _)
          (lp.norm_apply_le_norm two_ne_zero _ _) (norm_nonneg _) (norm_nonneg _)
      have hsm : Summable (fun n => ‖f.left n i * star (f.right n i)‖) :=
        Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb1 f.summable
      have : |d i| = ‖(d i : ℂ)‖ := by simp
      rw [this, hc]
      refine (norm_tsum_le_tsum_norm hsm).trans (le_of_eq ?_)
      refine tsum_congr (fun n => ?_)
      rw [norm_mul, norm_star]
    have hsm2 : ∀ i, Summable (fun n => ‖f.left n i‖ * ‖f.right n i‖) := by
      intro i
      refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) f.summable
      exact mul_le_mul (lp.norm_apply_le_norm two_ne_zero _ _)
          (lp.norm_apply_le_norm two_ne_zero _ _) (norm_nonneg _) (norm_nonneg _)
    calc ∑ i ∈ s, |d i| ≤ ∑ i ∈ s, ∑' n, ‖f.left n i‖ * ‖f.right n i‖ :=
          Finset.sum_le_sum (fun i _ => hb i)
      _ = ∑' n, ∑ i ∈ s, ‖f.left n i‖ * ‖f.right n i‖ :=
          (Summable.tsum_finsetSum (fun i _ => hsm2 i)).symm
      _ ≤ ∑' n, ‖f.left n‖ * ‖f.right n‖ := by
          refine Summable.tsum_le_tsum (fun n => g68i_cs_lp _ _ s) ?_ f.summable
          exact summable_sum (fun i _ => hsm2 i)

end G68ILIB

/-- IV.D, (4.46), p.9: gamma>0 ensures trace class; gamma<1/2 is not a density. -/
theorem solution (gamma : ℝ) (hgamma : 0 < gamma) :
    IsTraceClass (generalizedThermal gamma) ∧
    traceSize (generalizedThermal gamma) = ENNReal.ofReal (max 1 (1 / (2 * gamma))) ∧
    (1 / (gamma + 1 / 2)) *
      (∑' n : ℕ, |(gamma - 1 / 2) / (gamma + 1 / 2)| ^ n) =
      max 1 (1 / (2 * gamma)) := by
  have hp : 0 < gamma + 1 / 2 := by linarith
  set q := (gamma - 1 / 2) / (gamma + 1 / 2) with hq
  have hr0 : 0 ≤ |q| := abs_nonneg _
  have hr1 : |q| < 1 := by
    rw [hq, abs_div, abs_of_pos hp, div_lt_one hp, abs_lt]
    constructor <;> linarith
  have hgeo : (1 / (gamma + 1 / 2)) * (∑' n : ℕ, |q| ^ n) = max 1 (1 / (2 * gamma)) := by
    rw [tsum_geometric_of_lt_one hr0 hr1]
    rcases le_or_gt (1 / 2) gamma with h | h
    · have hqa : |q| = (gamma - 1 / 2) / (gamma + 1 / 2) := by
        rw [hq, abs_of_nonneg (div_nonneg (by linarith) hp.le)]
      have hm : max 1 (1 / (2 * gamma)) = 1 := by
        apply max_eq_left
        rw [div_le_one (by linarith)]; linarith
      rw [hm, hqa]
      field_simp
      ring
    · have hqa : |q| = (1 / 2 - gamma) / (gamma + 1 / 2) := by
        rw [hq, abs_of_neg (div_neg_of_neg_of_pos (by linarith) hp)]
        ring
      have hm : max 1 (1 / (2 * gamma)) = 1 / (2 * gamma) := by
        apply max_eq_right
        rw [le_div_iff₀ (by linarith)]; linarith
      rw [hm, hqa]
      field_simp
      ring_nf
      field_simp
  have hd : Summable (fun n : ℕ => |1 / (gamma + 1 / 2) * q ^ n|) := by
    have := (summable_geometric_of_lt_one hr0 hr1).mul_left (1 / (gamma + 1 / 2))
    refine this.congr (fun n => ?_)
    rw [abs_mul, abs_pow, abs_of_pos (by positivity : (0:ℝ) < 1 / (gamma + 1 / 2))]
  have hX : ∀ i j, generalizedThermal gamma i j =
      if i = j then ((1 / (gamma + 1 / 2) * q ^ i : ℝ) : ℂ) else 0 := by
    intro i j
    simp only [generalizedThermal, QAlgorithms.Papers.Independent.Dependency50.P39.thermalMatrix]
    split_ifs with h
    · subst h
      congr 2
      · field_simp
      · rw [hq]; congr 1; field_simp
    · rfl
  obtain ⟨h1, h2⟩ := g68i_diag_ts _ hd _ hX
  refine ⟨h1, ?_, hgeo⟩
  rw [h2, ← hgeo]
  congr 1
  rw [← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  rw [abs_mul, abs_pow, abs_of_pos (by positivity : (0:ℝ) < 1 / (gamma + 1 / 2))]



end

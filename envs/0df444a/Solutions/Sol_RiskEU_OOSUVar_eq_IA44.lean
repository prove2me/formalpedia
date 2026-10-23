-- Prove2me | solution 1 for RiskEU.OOSUVar.eq_IA44
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T11:04:22.029235+00:00
-- url     : https://prove2.me/submissions/76f17087-4afc-483b-b445-8de298ae9269
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting
import Theorems.Thm_RiskEU_OOSUVar_eq_IA43

open MeasureTheory ProbabilityTheory Matrix RiskEU.OOSUVar

private lemma vmv_mulVec {N : ℕ} (u v x : Fin N → ℝ) :
    vecMulVec u v *ᵥ x = (v ⬝ᵥ x) • u := by
  ext i
  simp only [vecMulVec, mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, of_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

private lemma quad_eq {N : ℕ} (μ : Fin N → ℝ) (A : Matrix (Fin N) (Fin N) ℝ) :
    ∑ i, ∑ j, μ i * μ j * A i j = μ ⬝ᵥ (A *ᵥ μ) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma muBmu {N : ℕ} (M : Market N) : M.mu ⬝ᵥ (M.B *ᵥ M.mu) = M.psi2 := by
  set S := M.Sigma⁻¹
  have hB : M.B *ᵥ M.mu = S *ᵥ M.mu - (M.wg ⬝ᵥ M.mu) • (S *ᵥ ones N) := by
    rw [Market.B, ← mulVec_mulVec, sub_mulVec, one_mulVec, mulVec_sub, vmv_mulVec, mulVec_smul]
  have hw : M.wg ⬝ᵥ M.mu = M.sigmaG2 * (M.mu ⬝ᵥ (S *ᵥ ones N)) := by
    rw [Market.wg, smul_dotProduct, dotProduct_comm]; rfl
  rw [hB, dotProduct_sub, dotProduct_smul, hw, Market.psi2, Market.muG]
  simp only [smul_eq_mul]
  by_cases h : M.sigmaG2 = 0
  · simp [h, S]
  · field_simp
    ring

private lemma quad_outer {N : ℕ} (μ : Fin N → ℝ) (B : Matrix (Fin N) (Fin N) ℝ) :
    μ ⬝ᵥ ((B * vecMulVec μ μ * B) *ᵥ μ) = (μ ⬝ᵥ (B *ᵥ μ)) * (μ ⬝ᵥ (B *ᵥ μ)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, vmv_mulVec, mulVec_smul, dotProduct_smul,
    smul_eq_mul]

theorem solution {N T : ℕ} (M : Market N) (hM : M.Standing T)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin T → Ω → EuclideanSpace ℝ (Fin N)) (hr : M.IsGaussianSample P r)
    (κ : ℝ) (hκ : κ ∈ Set.Icc (0 : ℝ) 1) :
    MemLp (fun ω => M.oosMean κ (sampleData r ω)) 2 P ∧
    variance (fun ω => M.oosMean κ (sampleData r ω)) P =
      M.sigmaG2 * M.psi2 / ((T : ℝ) - N - 1) +
        κ ^ 2 * M.psi2 / M.gamma ^ 2 *
          ((2 * (T : ℝ) * (N + 1) + (T : ℝ) ^ 2 * ((T : ℝ) - N - 3 + 2 * ((T : ℝ) - N) * M.psi2)) /
            (((T : ℝ) - N) * ((T : ℝ) - N - 1) ^ 2 * ((T : ℝ) - N - 3))) := by
  have h43 := eq_IA43 M hM P r hr κ hκ
  set W : Fin N → Ω → ℝ := fun i ω => M.wShrink κ (sampleData r ω) i with hW
  have hmem : ∀ i, MemLp (fun ω => M.mu i * W i ω) 2 P := fun i => (h43 i i).1.const_mul _
  have hfun : (fun ω => M.oosMean κ (sampleData r ω)) =
      ∑ i ∈ Finset.univ, (fun ω => M.mu i * W i ω) := by
    funext ω
    simp [Market.oosMean, dotProduct, W, mul_comm]
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact memLp_finsetSum' _ (fun i _ => hmem i)
  rw [hfun, variance_sum' (fun i _ => hmem i)]
  have hc : ∀ i j, cov[fun ω => M.mu i * W i ω, fun ω => M.mu j * W j ω; P] =
      M.mu i * M.mu j * cov[W i, W j; P] := by
    intro i j
    rw [covariance_const_mul_left, covariance_const_mul_right]; ring
  simp_rw [hc]
  simp only [W, fun i j => (h43 i j).2]
  rw [quad_eq, add_mulVec, smul_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
    dotProduct_smul, quad_outer, muBmu, smul_eq_mul, smul_eq_mul]
  obtain ⟨hN2, hNT, -, hγ⟩ := hM
  have hTN : (N : ℝ) + 7 < T := by exact_mod_cast hNT
  have h0 : (T : ℝ) - N ≠ 0 := by intro h; linarith
  have h1 : (T : ℝ) - N - 1 ≠ 0 := by intro h; linarith
  have h3 : (T : ℝ) - N - 3 ≠ 0 := by intro h; linarith
  have hg : M.gamma ≠ 0 := hγ.ne'
  field_simp
  ring

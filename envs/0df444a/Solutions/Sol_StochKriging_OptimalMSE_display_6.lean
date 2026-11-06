-- Prove2me | solution 1 for StochKriging.OptimalMSE.display_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T02:17:57.52351+00:00
-- url     : https://prove2.me/submissions/a6301f7e-f543-4c8a-91bc-93883b97e64b

import Mathlib
import Definitions.Def_StochKriging_OptimalMSE_Model

open MeasureTheory ProbabilityTheory Matrix

namespace StochKriging.OptimalMSE

section Aux

variable {Ω : Type*} {X : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {k : ℕ} {M : X → Ω → ℝ} {ε : ℕ → X → Ω → ℝ}

lemma aux_memLp_avgNoise (h : IsModel P M ε) (x : Fin k → X) (n : Fin k → ℕ) (i : Fin k) :
    MemLp (avgNoise ε x n i) 2 P := by
  have h1 : MemLp (fun ω => ∑ j ∈ Finset.range (n i), ε j (x i) ω) 2 P :=
    memLp_finsetSum _ (fun j _ => h.memLp_noise j (x i))
  have h2 := h1.const_mul ((n i : ℝ)⁻¹)
  have : avgNoise ε x n i = fun ω => (n i : ℝ)⁻¹ * ∑ j ∈ Finset.range (n i), ε j (x i) ω := by
    funext ω; simp [avgNoise, div_eq_inv_mul]
  rw [this]; exact h2

lemma aux_cov_field_avgNoise (h : IsModel P M ε) (y : X) (x : Fin k → X) (n : Fin k → ℕ)
    (j : Fin k) : cov[M y, avgNoise ε x n j; P] = 0 := by
  have : avgNoise ε x n j = fun ω => (fun ω' => ∑ r ∈ Finset.range (n j), ε r (x j) ω') ω
      / (n j : ℝ) := rfl
  rw [this, covariance_fun_div_right,
    covariance_fun_sum_right' (fun r _ => h.memLp_noise r (x j)) (h.memLp_field y)]
  simp [h.uncorrelated]

lemma aux_mse_eq (β₀ : ℝ) (x : Fin k → X) (n : Fin k → ℕ) (h : IsModel P M ε)
    (hn : ∀ i, 1 ≤ n i) (x₀ : X) (l₀ : ℝ) (l : Fin k → ℝ) :
    mse P (linPred l₀ l (sampleMean β₀ M ε x n)) (target β₀ M x₀) =
      (l₀ - β₀ + β₀ * ∑ i, l i) ^ 2 + l ⬝ᵥ ((SigmaM P M x + SigmaEps P ε x n) *ᵥ l)
        - 2 * (l ⬝ᵥ SigmaMCross P M x x₀) + SigmaMFun P M x₀ x₀ := by
  set U : Fin k → Ω → ℝ := fun i => M (x i) + avgNoise ε x n i with hU
  set Z : Ω → ℝ := (∑ i, l i • U i) - M x₀ with hZ
  set a := l₀ - β₀ + β₀ * ∑ i, l i with ha
  have hUm : ∀ i, MemLp (U i) 2 P := fun i => (h.memLp_field _).add (aux_memLp_avgNoise h x n i)
  have hlUm : ∀ i, MemLp (l i • U i) 2 P := fun i => (hUm i).const_smul (l i)
  have hSm : MemLp (∑ i, l i • U i) 2 P := memLp_finsetSum' _ (fun i _ => hlUm i)
  have hZm : MemLp Z 2 P := hSm.sub (h.memLp_field x₀)
  have hpt : ∀ ω, linPred l₀ l (sampleMean β₀ M ε x n) ω - target β₀ M x₀ ω = a + Z ω := by
    intro ω
    have hs : ∀ i, sampleMean β₀ M ε x n ω i = β₀ + U i ω := by
      intro i
      have hni : (n i : ℝ) ≠ 0 := by
        have := hn i; exact_mod_cast (by omega : n i ≠ 0)
      simp only [sampleMean, output, hU, avgNoise, Pi.add_apply, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
      ring
    simp only [linPred, target, dotProduct, hs, hZ, Pi.sub_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, ha, mul_add, Finset.sum_add_distrib]
    have : ∑ x, l x * β₀ = β₀ * ∑ i, l i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    rw [this]; ring
  have hZmean : ∫ ω, Z ω ∂P = 0 := by
    have hi : ∀ i, ∫ ω, U i ω ∂P = 0 := by
      intro i
      have hN : ∫ ω, avgNoise ε x n i ω ∂P = 0 := by
        simp only [avgNoise]
        rw [integral_div, integral_finset_sum _ (fun j _ =>
          (h.memLp_noise j (x i)).integrable one_le_two)]
        simp [h.mean_noise]
      rw [hU]
      simp only [Pi.add_apply]
      rw [integral_add ((h.memLp_field _).integrable one_le_two)
        ((aux_memLp_avgNoise h x n i).integrable one_le_two), h.mean_field, hN, add_zero]
    rw [hZ]
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_sub, integral_finset_sum, h.mean_field]
    · simp [integral_const_mul, hi]
    · exact fun i _ => ((hUm i).integrable one_le_two).const_mul _
    · exact integrable_finset_sum _ (fun i _ => ((hUm i).integrable one_le_two).const_mul _)
    · exact (h.memLp_field _).integrable one_le_two
  have hZZ : ∫ ω, Z ω ^ 2 ∂P = cov[Z, Z; P] := by
    simp [covariance, hZmean, pow_two]
  have hmse : mse P (linPred l₀ l (sampleMean β₀ M ε x n)) (target β₀ M x₀)
      = a ^ 2 + cov[Z, Z; P] := by
    unfold mse
    simp_rw [hpt]
    have : ∀ ω, (a + Z ω) ^ 2 = a ^ 2 + 2 * a * Z ω + Z ω ^ 2 := fun ω => by ring
    simp_rw [this]
    rw [integral_add, integral_add, integral_const, integral_const_mul, hZmean, hZZ]
    · simp
    · exact integrable_const _
    · exact (hZm.integrable one_le_two).const_mul _
    · exact (integrable_const _).add ((hZm.integrable one_le_two).const_mul _)
    · exact hZm.integrable_sq
  have hUU : ∀ i j, cov[U i, U j; P] = SigmaM P M x i j + SigmaEps P ε x n i j := by
    intro i j
    rw [covariance_add_left (h.memLp_field _) (aux_memLp_avgNoise h x n i) (hUm j),
      covariance_add_right (h.memLp_field _) (h.memLp_field _) (aux_memLp_avgNoise h x n j),
      covariance_add_right (aux_memLp_avgNoise h x n i) (h.memLp_field _)
        (aux_memLp_avgNoise h x n j),
      aux_cov_field_avgNoise h, covariance_comm (avgNoise ε x n i), aux_cov_field_avgNoise h]
    simp [SigmaM, SigmaEps, SigmaMFun]
  have hUV : ∀ i, cov[U i, M x₀; P] = SigmaMCross P M x x₀ i := by
    intro i
    rw [covariance_add_left (h.memLp_field _) (aux_memLp_avgNoise h x n i) (h.memLp_field _),
      covariance_comm (avgNoise ε x n i), aux_cov_field_avgNoise h]
    simp [SigmaMCross, SigmaMFun, covariance_comm]
  rw [hmse, hZ, covariance_sub_sub hSm (h.memLp_field x₀) hSm (h.memLp_field x₀),
    covariance_sum_sum hlUm hlUm, covariance_sum_left hlUm (h.memLp_field x₀),
    covariance_sum_right hlUm (h.memLp_field x₀)]
  simp only [covariance_smul_left, covariance_smul_right, hUU, hUV, covariance_comm (M x₀)]
  simp only [dotProduct, mulVec, Matrix.add_apply, Finset.mul_sum, SigmaMFun]
  rw [← Finset.mul_sum]
  have e1 : (∑ i, ∑ j, l j * (l i * (SigmaM P M x i j + SigmaEps P ε x n i j))) =
      ∑ i, ∑ j, l i * ((SigmaM P M x i j + SigmaEps P ε x n i j) * l j) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e1]; ring

lemma aux_symm {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ) (hS : S.IsHermitian) (u w : Fin k → ℝ) :
    u ⬝ᵥ (S *ᵥ w) = w ⬝ᵥ (S *ᵥ u) := by
  rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose]
  have : Sᵀ = S := by simpa using hS.eq
  rw [this]

lemma aux_complete {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ) (hS : S.PosDef) (c l : Fin k → ℝ) :
    l ⬝ᵥ (S *ᵥ l) - 2 * (l ⬝ᵥ c) =
      (l - S⁻¹ *ᵥ c) ⬝ᵥ (S *ᵥ (l - S⁻¹ *ᵥ c)) - c ⬝ᵥ (S⁻¹ *ᵥ c) := by
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit
  have hm : S *ᵥ (S⁻¹ *ᵥ c) = c := by rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  rw [mulVec_sub, hm, dotProduct_sub, sub_dotProduct, sub_dotProduct,
    aux_symm S hS.isHermitian (S⁻¹ *ᵥ c) l, hm, dotProduct_comm (S⁻¹ *ᵥ c) c]
  ring

lemma aux_nonneg {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ) (hS : S.PosDef) (d : Fin k → ℝ) :
    0 ≤ d ⬝ᵥ (S *ᵥ d) := by
  simpa using hS.posSemidef.dotProduct_mulVec_nonneg d

end Aux

section Main

variable {Ω : Type*} {X : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {k : ℕ} {M : X → Ω → ℝ} {ε : ℕ → X → Ω → ℝ}

lemma aux_key (β₀ : ℝ) (x : Fin k → X) (n : Fin k → ℕ) (h : IsModel P M ε)
    (hn : ∀ i, 1 ≤ n i) (hS : (SigmaM P M x + SigmaEps P ε x n).PosDef) (x₀ : X)
    (l₀ : ℝ) (l : Fin k → ℝ) :
    mse P (linPred l₀ l (sampleMean β₀ M ε x n)) (target β₀ M x₀) =
      (l₀ - β₀ + β₀ * ∑ i, l i) ^ 2 +
        (l - (SigmaM P M x + SigmaEps P ε x n)⁻¹ *ᵥ SigmaMCross P M x x₀) ⬝ᵥ
          ((SigmaM P M x + SigmaEps P ε x n) *ᵥ
            (l - (SigmaM P M x + SigmaEps P ε x n)⁻¹ *ᵥ SigmaMCross P M x x₀))
        + (SigmaMFun P M x₀ x₀ - SigmaMCross P M x x₀ ⬝ᵥ
            ((SigmaM P M x + SigmaEps P ε x n)⁻¹ *ᵥ SigmaMCross P M x x₀)) := by
  rw [aux_mse_eq β₀ x n h hn x₀ l₀ l]
  have := aux_complete _ hS (SigmaMCross P M x x₀) l
  linarith

end Main

end StochKriging.OptimalMSE

open StochKriging.OptimalMSE

theorem solution {Ω X : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {k : ℕ} (β₀ : ℝ) (M : X → Ω → ℝ) (ε : ℕ → X → Ω → ℝ) (x : Fin k → X) (n : Fin k → ℕ)
    (hmodel : IsModel P M ε) (hn : ∀ i, 1 ≤ n i)
    (hSig : (SigmaM P M x + SigmaEps P ε x n).PosDef) (x₀ : X) :
    (∀ ω, skPredictor P β₀ M ε x n x₀ ω =
        linPred
          (β₀ - β₀ * (((SigmaM P M x + SigmaEps P ε x n)⁻¹ *ᵥ SigmaMCross P M x x₀) ⬝ᵥ
            fun _ => 1))
          ((SigmaM P M x + SigmaEps P ε x n)⁻¹ *ᵥ SigmaMCross P M x x₀)
          (sampleMean β₀ M ε x n) ω) ∧
    (∀ (l₀ : ℝ) (l : Fin k → ℝ),
        mse P (skPredictor P β₀ M ε x n x₀) (target β₀ M x₀) ≤
          mse P (linPred l₀ l (sampleMean β₀ M ε x n)) (target β₀ M x₀)) ∧
    (∀ (l₀ : ℝ) (l : Fin k → ℝ),
        mse P (linPred l₀ l (sampleMean β₀ M ε x n)) (target β₀ M x₀) ≤
            mse P (skPredictor P β₀ M ε x n x₀) (target β₀ M x₀) →
          l = (SigmaM P M x + SigmaEps P ε x n)⁻¹ *ᵥ SigmaMCross P M x x₀ ∧
          l₀ = β₀ - β₀ * (((SigmaM P M x + SigmaEps P ε x n)⁻¹ *ᵥ SigmaMCross P M x x₀) ⬝ᵥ
            fun _ => 1)) := by
  set S := SigmaM P M x + SigmaEps P ε x n with hSdef
  set c := SigmaMCross P M x x₀ with hc
  set m := S⁻¹ *ᵥ c with hm
  set m₀ := β₀ - β₀ * (m ⬝ᵥ fun _ => 1) with hm₀
  have hsum : ∀ v : Fin k → ℝ, (v ⬝ᵥ fun _ => 1) = ∑ i, v i := by
    intro v; simp [dotProduct]
  have h1 : ∀ ω, skPredictor P β₀ M ε x n x₀ ω = linPred m₀ m (sampleMean β₀ M ε x n) ω := by
    intro ω
    simp only [skPredictor, linPred]
    rw [aux_symm _ hSig.inv.isHermitian c, ← hm, sub_dotProduct, smul_dotProduct, hm₀,
      smul_eq_mul, dotProduct_comm (sampleMean β₀ M ε x n ω) m,
      dotProduct_comm (fun _ => (1 : ℝ)) m]
    ring
  have hsk : skPredictor P β₀ M ε x n x₀ = linPred m₀ m (sampleMean β₀ M ε x n) := funext h1
  have hopt : mse P (skPredictor P β₀ M ε x n x₀) (target β₀ M x₀) =
      SigmaMFun P M x₀ x₀ - c ⬝ᵥ (S⁻¹ *ᵥ c) := by
    rw [hsk, aux_key β₀ x n hmodel hn hSig x₀ m₀ m, ← hSdef, ← hc, ← hm, hm₀, hsum m]
    simp
  refine ⟨h1, fun l₀ l => ?_, fun l₀ l hle => ?_⟩
  · rw [hopt, aux_key β₀ x n hmodel hn hSig x₀ l₀ l, ← hSdef, ← hc]
    nlinarith [aux_nonneg S hSig (l - S⁻¹ *ᵥ c), sq_nonneg (l₀ - β₀ + β₀ * ∑ i, l i)]
  · rw [hopt, aux_key β₀ x n hmodel hn hSig x₀ l₀ l, ← hSdef, ← hc] at hle
    have hq := aux_nonneg S hSig (l - S⁻¹ *ᵥ c)
    have hsq := sq_nonneg (l₀ - β₀ + β₀ * ∑ i, l i)
    have hq0 : (l - S⁻¹ *ᵥ c) ⬝ᵥ (S *ᵥ (l - S⁻¹ *ᵥ c)) = 0 := by linarith
    have ha0 : (l₀ - β₀ + β₀ * ∑ i, l i) ^ 2 = 0 := by linarith
    have hd : l - S⁻¹ *ᵥ c = 0 := by
      by_contra hne
      have := hSig.dotProduct_mulVec_pos hne
      simp only [star_trivial] at this
      linarith
    have hl : l = m := sub_eq_zero.mp hd
    refine ⟨hl, ?_⟩
    have : l₀ - β₀ + β₀ * ∑ i, l i = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ha0
    rw [hm₀, hsum, ← hl]
    linarith

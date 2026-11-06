-- Prove2me | solution 1 for StochKriging.OptimalMSE.display_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T02:17:56.723213+00:00
-- url     : https://prove2.me/submissions/900eb3db-91b2-4f42-b069-f6d9a472e985

import Mathlib
import Definitions.Def_StochKriging_OptimalMSE_Model

open MeasureTheory ProbabilityTheory Matrix

namespace StochKriging.OptimalMSE

universe u v

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

lemma aux_optimalMSE (β₀ : ℝ) (x : Fin k → X) (n : Fin k → ℕ) (h : IsModel P M ε)
    (hn : ∀ i, 1 ≤ n i) (hS : (SigmaM P M x + SigmaEps P ε x n).PosDef) (x₀ : X) :
    optimalMSE P β₀ M ε x n x₀ =
      SigmaMFun P M x₀ x₀ - SigmaMCross P M x x₀ ⬝ᵥ
        ((SigmaM P M x + SigmaEps P ε x n)⁻¹ *ᵥ SigmaMCross P M x x₀) := by
  set S := SigmaM P M x + SigmaEps P ε x n with hSdef
  set c := SigmaMCross P M x x₀
  have key : ∀ p : ℝ × (Fin k → ℝ),
      mse P (linPred p.1 p.2 (sampleMean β₀ M ε x n)) (target β₀ M x₀) =
        (p.1 - β₀ + β₀ * ∑ i, p.2 i) ^ 2 + (p.2 - S⁻¹ *ᵥ c) ⬝ᵥ (S *ᵥ (p.2 - S⁻¹ *ᵥ c))
          + (SigmaMFun P M x₀ x₀ - c ⬝ᵥ (S⁻¹ *ᵥ c)) := by
    intro p
    rw [aux_mse_eq β₀ x n h hn x₀ p.1 p.2]
    have := aux_complete S hS c p.2
    linarith
  unfold optimalMSE
  apply le_antisymm
  · set m := S⁻¹ *ᵥ c
    refine (ciInf_le ⟨SigmaMFun P M x₀ x₀ - c ⬝ᵥ (S⁻¹ *ᵥ c), ?_⟩
      ((β₀ - β₀ * ∑ i, m i, m) : ℝ × (Fin k → ℝ))).trans ?_
    · rintro _ ⟨p, rfl⟩
      simp only
      rw [key p]
      nlinarith [aux_nonneg S hS (p.2 - S⁻¹ *ᵥ c), sq_nonneg (p.1 - β₀ + β₀ * ∑ i, p.2 i)]
    · rw [key]; simp
  · refine le_ciInf fun p => ?_
    rw [key p]
    nlinarith [aux_nonneg S hS (p.2 - S⁻¹ *ᵥ c), sq_nonneg (p.1 - β₀ + β₀ * ∑ i, p.2 i)]

end Main

/-- `Ξ(A, B) = (A + A B⁻¹ A)⁻¹ = A⁻¹ - (A + B)⁻¹`. -/
noncomputable def Xi {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  (A + A * B⁻¹ * A)⁻¹

lemma Xi_posDef {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ) (hA : A.PosDef) (hB : B.PosDef) :
    (Xi A B).PosDef := by
  have h1 : (A * B⁻¹ * A).PosSemidef := by
    have := hB.inv.posSemidef.conjTranspose_mul_mul_same A
    rwa [hA.isHermitian.eq] at this
  exact (hA.add_posSemidef h1).inv

lemma Xi_eq {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ) (hA : A.PosDef) (hB : B.PosDef) :
    Xi A B = A⁻¹ - (A + B)⁻¹ := by
  have hAd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hBd : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit
  have hABd : IsUnit (A + B).det := (Matrix.isUnit_iff_isUnit_det _).mp (hA.add hB).isUnit
  unfold Xi
  apply Matrix.inv_eq_right_inv
  have hC : A + A * B⁻¹ * A = A * B⁻¹ * (A + B) := by
    rw [Matrix.mul_add, Matrix.mul_assoc A B⁻¹ B, nonsing_inv_mul _ hBd, Matrix.mul_one,
      add_comm]
  rw [hC, Matrix.mul_sub, Matrix.mul_assoc, Matrix.mul_assoc (A * B⁻¹) (A + B) (A + B)⁻¹,
    mul_nonsing_inv _ hABd, Matrix.mul_one, Matrix.add_mul, mul_nonsing_inv _ hAd,
    Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc (A * B⁻¹) B A⁻¹,
    Matrix.mul_assoc A B⁻¹ B, nonsing_inv_mul _ hBd, Matrix.mul_one, mul_nonsing_inv _ hAd]
  abel

end StochKriging.OptimalMSE

open StochKriging.OptimalMSE

universe u v

theorem solution (k : ℕ) :
    ∃ Ξ : Matrix (Fin k) (Fin k) ℝ → Matrix (Fin k) (Fin k) ℝ → Matrix (Fin k) (Fin k) ℝ,
      (∀ A B : Matrix (Fin k) (Fin k) ℝ, A.PosDef → B.PosDef → (Ξ A B).PosDef) ∧
      ∀ (Ω : Type u) (X : Type v) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (β₀ : ℝ) (M : X → Ω → ℝ) (ε : ℕ → X → Ω → ℝ) (x : Fin k → X) (n : Fin k → ℕ),
        IsModel P M ε → (∀ i, 1 ≤ n i) →
        (SigmaM P M x).PosDef → (SigmaEps P ε x n).PosDef →
        ∀ x₀ : X,
          optimalMSE P β₀ M ε x n x₀ =
              SigmaMFun P M x₀ x₀ - SigmaMCross P M x x₀ ⬝ᵥ
                ((SigmaM P M x + SigmaEps P ε x n)⁻¹ *ᵥ SigmaMCross P M x x₀) ∧
          optimalMSE P β₀ M ε x n x₀ =
              (SigmaMFun P M x₀ x₀ - SigmaMCross P M x x₀ ⬝ᵥ
                ((SigmaM P M x)⁻¹ *ᵥ SigmaMCross P M x x₀)) +
              SigmaMCross P M x x₀ ⬝ᵥ
                (Ξ (SigmaM P M x) (SigmaEps P ε x n) *ᵥ SigmaMCross P M x x₀) ∧
          (SigmaMCross P M x x₀ ≠ 0 →
            SigmaMFun P M x₀ x₀ - SigmaMCross P M x x₀ ⬝ᵥ
                ((SigmaM P M x)⁻¹ *ᵥ SigmaMCross P M x x₀) <
              optimalMSE P β₀ M ε x n x₀) := by
  refine ⟨Xi, Xi_posDef, ?_⟩
  intro Ω X _ P _ β₀ M ε x n h hn hA hB x₀
  have h1 := aux_optimalMSE β₀ x n h hn (hA.add hB) x₀
  have h2 : optimalMSE P β₀ M ε x n x₀ =
      (SigmaMFun P M x₀ x₀ - SigmaMCross P M x x₀ ⬝ᵥ
        ((SigmaM P M x)⁻¹ *ᵥ SigmaMCross P M x x₀)) +
      SigmaMCross P M x x₀ ⬝ᵥ (Xi (SigmaM P M x) (SigmaEps P ε x n) *ᵥ SigmaMCross P M x x₀) := by
    rw [h1, Xi_eq _ _ hA hB, sub_mulVec, dotProduct_sub]
    ring
  refine ⟨h1, h2, fun hc => ?_⟩
  rw [h2]
  have := (Xi_posDef _ _ hA hB).dotProduct_mulVec_pos hc
  simp only [star_trivial] at this
  linarith

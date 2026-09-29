-- Prove2me | solution 1 for PolyhedralSOC.Sandwich.interpolated_point_feasible
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T22:38:08.474099+00:00
-- url     : https://prove2.me/submissions/5e6e1336-ae65-49df-bf07-29a15385c8ec

import Mathlib
import Definitions.Def_PolyhedralSOC_Sandwich_CQP
import Definitions.Def_PolyhedralSOC_Sandwich_Conditions

namespace PolyhedralSOC.Sandwich

open Matrix

/-- The Euclidean norm `eucNorm` satisfies the triangle inequality (Cauchy–Schwarz). -/
private theorem eucNorm_add_le {k : ℕ} (u v : Fin k → ℝ) :
    eucNorm (u + v) ≤ eucNorm u + eucNorm v := by
  have hA : (0:ℝ) ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : (0:ℝ) ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcs : ∑ i, u i * v i ≤ Real.sqrt (∑ i, u i ^ 2) * Real.sqrt (∑ i, v i ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ u v
  have hpt : ∀ i : Fin k, (u + v) i ^ 2 = u i ^ 2 + 2 * (u i * v i) + v i ^ 2 := by
    intro i
    simp only [Pi.add_apply]
    ring
  have hexp : ∑ i, (u + v) i ^ 2
      = (∑ i, u i ^ 2) + 2 * (∑ i, u i * v i) + (∑ i, v i ^ 2) := by
    rw [Finset.sum_congr rfl fun i _ => hpt i, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 : Real.sqrt (∑ i, u i ^ 2) ^ 2 = ∑ i, u i ^ 2 := Real.sq_sqrt hA
  have h2 : Real.sqrt (∑ i, v i ^ 2) ^ 2 = ∑ i, v i ^ 2 := Real.sq_sqrt hB
  have hkey : ∑ i, (u + v) i ^ 2
      ≤ (Real.sqrt (∑ i, u i ^ 2) + Real.sqrt (∑ i, v i ^ 2)) ^ 2 := by
    rw [hexp]
    nlinarith [hcs, h1, h2]
  calc eucNorm (u + v) = Real.sqrt (∑ i, (u + v) i ^ 2) := rfl
    _ ≤ Real.sqrt ((Real.sqrt (∑ i, u i ^ 2) + Real.sqrt (∑ i, v i ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt hkey
    _ = eucNorm u + eucNorm v := by
        rw [Real.sqrt_sq (by positivity)]
        rfl

private theorem eucNorm_smul {k : ℕ} {c : ℝ} (hc : 0 ≤ c) (u : Fin k → ℝ) :
    eucNorm (c • u) = c * eucNorm u := by
  have hsum : ∑ i, (c • u) i ^ 2 = c ^ 2 * ∑ i, u i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  calc eucNorm (c • u) = Real.sqrt (∑ i, (c • u) i ^ 2) := rfl
    _ = Real.sqrt (c ^ 2 * ∑ i, u i ^ 2) := by rw [hsum]
    _ = c * eucNorm u := by
        rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
        rfl

/-- The interpolated point `(1−δ)y + δx̄` is feasible for (CQP). -/
private theorem interp_feasible {n k₀ m : ℕ} (P : CQP n k₀ m)
    (xbar : Fin n → ℝ) (r : ℝ) (hi : IsStrictlyFeasible P xbar r)
    (ε : ℝ) (hε : 0 < ε) (y : Fin n → ℝ) (hy : y ∈ feasRelaxed P ε)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδ : ∀ l, ε * (P.c l ⬝ᵥ y - P.d l) / (r + ε * (P.c l ⬝ᵥ y - P.d l)) ≤ δ) :
    (1 - δ) • y + δ • xbar ∈ feas P := by
  obtain ⟨hr, hlinbar, hconebar⟩ := hi
  obtain ⟨hliny, hconey⟩ := hy
  have h1δ : (0:ℝ) ≤ 1 - δ := by linarith
  refine ⟨?_, ?_⟩
  · intro i
    have e : (P.A *ᵥ ((1 - δ) • y + δ • xbar)) i
        = (1 - δ) * (P.A *ᵥ y) i + δ * (P.A *ᵥ xbar) i := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
      simp
    rw [e]
    have t1 : 0 ≤ (1 - δ) * ((P.A *ᵥ y) i - P.b i) :=
      mul_nonneg h1δ (by linarith [hliny i])
    have t2 : 0 ≤ δ * ((P.A *ᵥ xbar) i - P.b i) :=
      mul_nonneg hδ0 (by linarith [hlinbar i])
    nlinarith [t1, t2]
  · intro l
    set t : ℝ := P.c l ⬝ᵥ y - P.d l with ht
    set s : ℝ := P.c l ⬝ᵥ xbar - P.d l with hs
    have hny := hconey l
    have hnb := hconebar l
    have hny0 : (0:ℝ) ≤ eucNorm (P.Aℓ l *ᵥ y - P.bℓ l) := Real.sqrt_nonneg _
    have hnb0 : (0:ℝ) ≤ eucNorm (P.Aℓ l *ᵥ xbar - P.bℓ l) := Real.sqrt_nonneg _
    have htnn : 0 ≤ t := by nlinarith [hny, hny0]
    -- the interpolation identity for the conic data
    have edecomp : P.Aℓ l *ᵥ ((1 - δ) • y + δ • xbar) - P.bℓ l
        = (1 - δ) • (P.Aℓ l *ᵥ y - P.bℓ l) + δ • (P.Aℓ l *ᵥ xbar - P.bℓ l) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have ec : P.c l ⬝ᵥ ((1 - δ) • y + δ • xbar) - P.d l = (1 - δ) * t + δ * s := by
      rw [ht, hs]
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
      ring
    rw [edecomp, ec]
    have htri := eucNorm_add_le ((1 - δ) • (P.Aℓ l *ᵥ y - P.bℓ l))
      (δ • (P.Aℓ l *ᵥ xbar - P.bℓ l))
    rw [eucNorm_smul h1δ, eucNorm_smul hδ0] at htri
    -- the choice of δ absorbs the ε-relaxation
    have hden : 0 < r + ε * t := by nlinarith
    have hfrac : ε * t ≤ δ * (r + ε * t) := by
      have h := hδ l
      rw [← ht] at h
      rw [div_le_iff₀ hden] at h
      linarith
    have hgap : (1 - δ) * (ε * t) ≤ δ * r := by nlinarith [hfrac]
    have b1 : (1 - δ) * eucNorm (P.Aℓ l *ᵥ y - P.bℓ l) ≤ (1 - δ) * ((1 + ε) * t) :=
      mul_le_mul_of_nonneg_left hny h1δ
    have b2 : δ * eucNorm (P.Aℓ l *ᵥ xbar - P.bℓ l) ≤ δ * (s - r) :=
      mul_le_mul_of_nonneg_left hnb hδ0
    nlinarith [htri, b1, b2, hgap]

end PolyhedralSOC.Sandwich

open Matrix

theorem solution {n k₀ m : ℕ} (P : PolyhedralSOC.Sandwich.CQP n k₀ m)
    (xbar : Fin n → ℝ) (r : ℝ) (hi : PolyhedralSOC.Sandwich.IsStrictlyFeasible P xbar r)
    (ε : ℝ) (hε : 0 < ε) (y : Fin n → ℝ)
    (hy : y ∈ PolyhedralSOC.Sandwich.feasRelaxed P ε)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδ : ∀ ℓ, ε * (P.c ℓ ⬝ᵥ y - P.d ℓ) / (r + ε * (P.c ℓ ⬝ᵥ y - P.d ℓ)) ≤ δ) :
    (1 - δ) • y + δ • xbar ∈ PolyhedralSOC.Sandwich.feas P :=
  PolyhedralSOC.Sandwich.interp_feasible P xbar r hi ε hε y hy δ hδ0 hδ1 hδ

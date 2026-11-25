-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:20:23.55379+00:00
-- url     : https://prove2.me/submissions/33d4193f-ca58-48d2-ac44-9a98b019f817

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qh19_trace_pow_eq_zero_of_le_dim__a8f51753728b
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TracePowEqZeroOfLeDim
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
section Newton
open Polynomial
private theorem trace_pow_eq_zero_of_le_dim {K : Type*} [Field K] (r : ℕ)
    (N : Matrix (Fin r) (Fin r) K) (h : ∀ k, 1 ≤ k → k ≤ r → (N ^ k).trace = 0) :
    ∀ k, 1 ≤ k → (N ^ k).trace = 0 := by
  first | exact _root_.P2M_UpperTheory_Reformulated_B_Qh19_trace_pow_eq_zero_of_le_dim__a8f51753728b .. | (apply _root_.P2M_UpperTheory_Reformulated_B_Qh19_trace_pow_eq_zero_of_le_dim__a8f51753728b <;> assumption) | (intros; apply _root_.P2M_UpperTheory_Reformulated_B_Qh19_trace_pow_eq_zero_of_le_dim__a8f51753728b <;> assumption) | (apply @_root_.P2M_UpperTheory_Reformulated_B_Qh19_trace_pow_eq_zero_of_le_dim__a8f51753728b <;> assumption) | (intros; apply @_root_.P2M_UpperTheory_Reformulated_B_Qh19_trace_pow_eq_zero_of_le_dim__a8f51753728b <;> assumption) | (apply @_root_.P2M_UpperTheory_Reformulated_B_Qh19_trace_pow_eq_zero_of_le_dim__a8f51753728b <;> first | assumption | infer_instance)
private theorem trace_aeval_X_mul {K : Type*} [Field K] {n : ℕ} (N : Matrix (Fin n) (Fin n) K)
    (h : ∀ k : ℕ, (N ^ (k + 1)).trace = 0) (p : K[X]) :
    (aeval N (X * p)).trace = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, map_add, Matrix.trace_add, hp, hq, add_zero]
  | monomial n a =>
    rw [show (X * monomial n a : K[X]) = monomial (n + 1) a by
      rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial]; ring]
    rw [aeval_monomial, ← Algebra.smul_def, Matrix.trace_smul, h, smul_zero]
private theorem isNilpotent_of_trace_pow_succ {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) K) (h : ∀ k : ℕ, (N ^ (k + 1)).trace = 0) : IsNilpotent N := by
  classical
  have hint : IsIntegral K N := Algebra.IsIntegral.isIntegral N
  have hμ : minpoly K N ≠ 0 := minpoly.ne_zero hint
  obtain ⟨q, hq, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd (minpoly K N) hμ 0
  set m := (minpoly K N).rootMultiplicity 0
  simp only [map_zero, sub_zero] at hq hnd
  have hcop : IsCoprime (X ^ (m + 1)) q :=
    ((Polynomial.irreducible_X).coprime_iff_not_dvd.mpr hnd).pow_left
  obtain ⟨u, v, huv⟩ := hcop
  have hXq : aeval N (X ^ (m + 1) * q) = 0 := by
    rw [show (X ^ (m + 1) * q : K[X]) = X * minpoly K N by rw [hq]; ring, map_mul,
      minpoly.aeval, mul_zero]
  have h1 : aeval N (u * X ^ (m + 1)) + aeval N (v * q) = 1 := by
    rw [← map_add, huv, map_one]
  have hprod : aeval N (u * X ^ (m + 1)) * aeval N (v * q) = 0 := by
    rw [← map_mul, show (u * X ^ (m + 1) * (v * q) : K[X]) = u * v * (X ^ (m + 1) * q) by ring,
      map_mul, hXq, mul_zero]
  set e := aeval N (u * X ^ (m + 1)) with he_def
  have he : IsIdempotentElem e := by
    have : aeval N (v * q) = 1 - e := by rw [← h1]; abel
    rw [this, mul_sub, mul_one, sub_eq_zero] at hprod
    exact hprod.symm
  have hτ : e.trace = 0 := by
    rw [he_def, show (u * X ^ (m + 1) : K[X]) = X * (u * X ^ m) by ring]
    exact trace_aeval_X_mul N h _
  have hle : IsIdempotentElem (Matrix.toLin' e) := by
    have h3 := Matrix.toLin'_mul e e
    rw [he.eq] at h3
    exact h3.symm
  have hl0 := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hle (by rw [Matrix.trace_toLin'_eq, hτ])
  have he0 : e = 0 := Matrix.toLin'.map_eq_zero_iff.mp hl0
  have hvq : aeval N (v * q) = 1 := by rw [← h1, he0, zero_add]
  refine ⟨m + 1, ?_⟩
  calc N ^ (m + 1) = N ^ (m + 1) * aeval N (v * q) := by rw [hvq, mul_one]
    _ = aeval N (v * (X ^ (m + 1) * q)) := by
        rw [show (v * (X ^ (m + 1) * q) : K[X]) = X ^ (m + 1) * (v * q) by ring,
          map_mul (aeval N) (X ^ (m + 1)), map_pow, aeval_X]
    _ = 0 := by rw [map_mul, hXq, mul_zero]
end Newton
end
end ReciprocityTheory.L2DbarEstimates.Y
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {K : Type*} [Field K] [CharZero K] (r : ℕ)
    (N : Matrix (Fin r) (Fin r) K) (h : ∀ k, 1 ≤ k → k ≤ r → (N ^ k).trace = 0) :
    IsNilpotent N :=
  isNilpotent_of_trace_pow_succ N fun k => trace_pow_eq_zero_of_le_dim r N h (k + 1) (by omega)
end ReciprocityTheory.L2DbarEstimates.Y

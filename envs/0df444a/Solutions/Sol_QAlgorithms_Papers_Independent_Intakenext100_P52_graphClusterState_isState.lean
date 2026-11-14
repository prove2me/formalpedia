-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P52.graphClusterState_isState
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T04:12:07.737208+00:00
-- url     : https://prove2.me/submissions/3212a8c4-e4ba-4711-b704-389de2681830

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52
noncomputable section
open QAlgorithms QAlgorithms.Papers.Independent.Intakenext100.P52 QAlgorithms.Papers.Independent.Information100.P21 QAlgorithms.Papers.Independent.Gap20.P01
open scoped Matrix ComplexConjugate
private theorem edgePhase_norm {V : Type*} [DecidableEq V] (E : Finset (V × V)) (z : V → Bool) :
    ‖edgePhase E z‖ = 1 := by
  simp only [edgePhase, norm_prod]
  apply Finset.prod_eq_one
  intro e he
  cases z e.1 <;> cases z e.2 <;> simp [czPhase]


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) : IsState (graphClusterState E) := by
  have hs2 : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hn : (2 : ℝ) ^ Fintype.card V ≠ 0 := pow_ne_zero _ (by norm_num)
  have hsq : ‖graphClusterState E‖ ^ 2 = 1 := by
    simp only [EuclideanSpace.norm_sq_eq, graphClusterState, PiLp.toLp_apply,
      norm_mul, norm_pow, edgePhase_norm, mul_one, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
    simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul,
      Nat.mul_comm (Fintype.card V) 2, pow_mul, inv_pow, hs2]
    rw [← pow_mul, mul_comm (Fintype.card V) 2, pow_mul, hs2]
    exact mul_inv_cancel₀ hn
  change ‖graphClusterState E‖ = 1
  nlinarith [norm_nonneg (graphClusterState E)]
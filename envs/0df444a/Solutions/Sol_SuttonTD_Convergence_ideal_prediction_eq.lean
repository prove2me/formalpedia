-- Prove2me | solution 1 for SuttonTD.Convergence.ideal_prediction_eq
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:14:28.912973+00:00
-- url     : https://prove2.me/submissions/0cfd0135-75bd-456c-a076-ab89c575e2ff

import Mathlib
import Definitions.Def_SuttonTD_Convergence_AbsorbingChain
set_option autoImplicit false
open Filter Topology Matrix SuttonTD.Convergence

lemma sutton_summable {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : Tendsto (fun n : ℕ => A ^ n) atTop (𝓝 0)) :
    Summable (fun i : ℕ => A ^ i) := by
  letI : NormedRing (Matrix ι ι ℝ) := Matrix.linftyOpNormedRing
  letI : NormedSpace ℝ (Matrix ι ι ℝ) := Matrix.linftyOpNormedSpace
  haveI : CompleteSpace (Matrix ι ι ℝ) := FiniteDimensional.complete ℝ (Matrix ι ι ℝ)
  have hA' : Tendsto (fun n : ℕ => A ^ n) atTop (𝓝 0) := hA
  have hn : Tendsto (fun n : ℕ => ‖A ^ n‖) atTop (𝓝 0) := by
    simpa using hA'.norm
  obtain ⟨N, hN, hN1⟩ := ((hn.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))).and
    (eventually_ge_atTop 1)).exists
  set q : ℝ := ‖A ^ N‖ with hq
  have hq0 : 0 ≤ q := norm_nonneg _
  have hq1 : q < 1 := hN
  set s : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, ‖A ^ i‖ with hs
  set M : ℝ := s N with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hmono : ∀ n m, n ≤ m → s n ≤ s m := fun n m h =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun i _ _ => norm_nonneg _)
  have hrec : ∀ n, s (n + N) ≤ M + q * s n := by
    intro n
    have : s (n + N) = s N + ∑ i ∈ Finset.range n, ‖A ^ (N + i)‖ := by
      simp only [hs]
      rw [add_comm n N, Finset.sum_range_add]
    rw [this]
    have h2 : ∑ i ∈ Finset.range n, ‖A ^ (N + i)‖ ≤ ∑ i ∈ Finset.range n, q * ‖A ^ i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [pow_add]
      exact norm_mul_le _ _
    rw [← Finset.mul_sum] at h2
    simp only [hs, hM] at h2 ⊢
    linarith
  have hbound : ∀ n, s n ≤ M / (1 - q) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      have h1q : 0 < 1 - q := by linarith
      by_cases hn : n < N
      · calc s n ≤ s N := hmono _ _ hn.le
          _ ≤ M / (1 - q) := by
            rw [le_div_iff₀ h1q]
            nlinarith
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + N := ⟨n - N, by omega⟩
        have ihm : s m ≤ M / (1 - q) := ih m (by omega)
        calc s (m + N) ≤ M + q * s m := hrec m
          _ ≤ M + q * (M / (1 - q)) := by gcongr
          _ = M / (1 - q) := by field_simp; ring
  have hsum : Summable (fun i : ℕ => ‖A ^ i‖) :=
    summable_of_sum_range_le (fun i => norm_nonneg _) hbound
  exact hsum.of_norm

theorem sutton_neumann {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : Tendsto (fun n : ℕ => A ^ n) atTop (𝓝 0)) :
    IsUnit (1 - A) ∧ HasSum (fun i : ℕ => A ^ i) (1 - A)⁻¹ := by
  have hu : IsUnit (1 - A) := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro x y hxy
    have h0 : (1 - A).mulVec (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    set z := x - y with hz
    have hAz : A.mulVec z = z := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
      exact h0.symm
    have hpow : ∀ n : ℕ, (A ^ n).mulVec z = z := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, hAz]
    have hcont : Continuous (fun M : Matrix ι ι ℝ => M.mulVec z) :=
      Continuous.matrix_mulVec continuous_id continuous_const
    have ht : Tendsto (fun n : ℕ => (A ^ n).mulVec z) atTop (𝓝 ((0 : Matrix ι ι ℝ).mulVec z)) :=
      (hcont.tendsto 0).comp hA
    simp only [hpow, Matrix.zero_mulVec] at ht
    have : z = 0 := tendsto_nhds_unique tendsto_const_nhds ht
    exact sub_eq_zero.mp this
  refine ⟨hu, ?_⟩
  obtain ⟨S, hS⟩ := (sutton_summable A hA)
  have hdet : IsUnit (1 - A).det := (Matrix.isUnit_iff_isUnit_det _).mp hu
  have hpart : ∀ n : ℕ, ∑ i ∈ Finset.range n, A ^ i = (1 - A ^ n) * (1 - A)⁻¹ := by
    intro n
    have h := geom_sum_mul_neg A n
    calc ∑ i ∈ Finset.range n, A ^ i
        = (∑ i ∈ Finset.range n, A ^ i) * ((1 - A) * (1 - A)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hdet, mul_one]
      _ = (1 - A ^ n) * (1 - A)⁻¹ := by rw [← mul_assoc, h]
  have h1 : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, A ^ i) atTop (𝓝 S) :=
    hS.tendsto_sum_nat
  have h2 : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, A ^ i) atTop (𝓝 ((1 - 0) * (1 - A)⁻¹)) := by
    simp only [hpart]
    exact (tendsto_const_nhds.sub hA).mul tendsto_const_nhds
  have : S = (1 - A)⁻¹ := by
    have := tendsto_nhds_unique h1 h2
    simpa using this
  rw [← this]
  exact hS

theorem solution {N T : Type*} [Fintype N] [DecidableEq N] [Fintype T]
    (C : AbsorbingChain N T) (zbar : T → ℝ) (i : N) :
    HasSum (fun k : ℕ => (C.Q ^ k *ᵥ C.h zbar) i) (((1 - C.Q)⁻¹ *ᵥ C.h zbar) i) := by
  have hN := (sutton_neumann C.Q C.absorbing).2
  let f : Matrix N N ℝ →+ ℝ :=
    { toFun := fun M => (M *ᵥ C.h zbar) i
      map_zero' := by simp
      map_add' := by intro a b; simp [Matrix.add_mulVec] }
  have hc : Continuous f := by
    show Continuous (fun M : Matrix N N ℝ => (M *ᵥ C.h zbar) i)
    exact (continuous_apply i).comp (Continuous.matrix_mulVec continuous_id continuous_const)
  exact hN.map f hc

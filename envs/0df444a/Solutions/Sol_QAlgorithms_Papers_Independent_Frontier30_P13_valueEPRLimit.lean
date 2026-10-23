-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P13.valueEPRLimit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T13:13:50.868+00:00
-- url     : https://prove2.me/submissions/273b2985-6f2f-4dc8-b81f-338fede273c9

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P13

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify physicalCovariance)

open scoped ComplexOrder

attribute [local instance] Classical.decEq

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier30.P13

open Matrix

theorem x8_phys_psd {n : Type*} [Fintype n] {G J : Matrix n n ℝ} (h : physicalCovariance G J) :
    G.PosSemidef := by
  obtain ⟨hT, hP⟩ := h
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hT]
  · have := hP.dotProduct_mulVec_nonneg (fun i => (x i : ℂ))
    have hre := (Complex.nonneg_iff.1 this).1
    refine le_of_le_of_eq hre ?_
    simp [dotProduct, mulVec, complexify, Complex.re_sum, Finset.mul_sum, sub_mul, mul_sub]

theorem x8_quad {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) (hM : M.PosSemidef)
    (a b : n) (s : ℝ) :
    0 ≤ M a a + s * M a b + s * M b a + s * s * M b b := by
  have := hM.dotProduct_mulVec_nonneg (Pi.single a 1 + Pi.single b s)
  refine le_of_le_of_eq this ?_
  simp [mulVec_add, dotProduct_add, add_dotProduct, mulVec_single, single_dotProduct]
  ring

theorem x8_uncert {A : Type*} [Fintype A] (GA : Matrix (ModeQuadrature A) (ModeQuadrature A) ℝ)
    (h : physicalCovariance GA (phaseJ A)) (m : A) :
    2 ≤ GA (m, false) (m, false) + GA (m, true) (m, true) := by
  have := h.2.dotProduct_mulVec_nonneg (Pi.single (m, false) 1 + Pi.single (m, true) Complex.I)
  have hre := (Complex.nonneg_iff.1 this).1
  simp [mulVec_add, dotProduct_add, add_dotProduct, mulVec_single,
    single_dotProduct, complexify, phaseJ] at hre
  linarith

theorem x8_bound (n : ℕ) (hn : 0 < n) (r p : ℝ) (hp : feasibleScale (squeezedCM n r) p) :
    p ≤ 2 * Real.exp (-r) := by
  obtain ⟨hp0, -, GA, GB, hA, hB, hD⟩ := hp
  set m : Fin n := ⟨0, hn⟩
  have hBpsd := x8_phys_psd hB
  have h1 := x8_quad _ hD (Sum.inl (m, false)) (Sum.inr (m, false)) (-1)
  have h2 := x8_quad _ hD (Sum.inl (m, true)) (Sum.inr (m, true)) 1
  have h3 := x8_uncert GA hA m
  have h4 := hBpsd.diag_nonneg (i := (m, false))
  have h5 := hBpsd.diag_nonneg (i := (m, true))
  simp [squeezedCM, reversal, fromBlocks] at h1 h2
  have e : Real.cosh r - Real.sinh r = Real.exp (-r) := Real.cosh_sub_sinh r
  nlinarith

theorem x8_main (n : ℕ) (hn : 0 < n) :
    Tendsto (fun r : ℝ => valueV (squeezedCM n r)) atTop (nhds 0) := by
  have hup : ∀ r, valueV (squeezedCM n r) ≤ 2 * Real.exp (-r) := by
    intro r
    by_cases hne : {p | feasibleScale (squeezedCM n r) p}.Nonempty
    · exact csSup_le hne fun p hp => x8_bound n hn r p hp
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      unfold valueV; rw [hne, Real.sSup_empty]; positivity
  have hlo : ∀ r, 0 ≤ valueV (squeezedCM n r) := fun r => Real.sSup_nonneg fun _ hp => hp.1
  have ht : Tendsto (fun r : ℝ => 2 * Real.exp (-r)) atTop (nhds 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero).const_mul 2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht hlo hup

end QAlgorithms.Papers.Independent.Frontier30.P13

open QAlgorithms.Papers.Independent.Frontier30.P13 in
theorem solution (n : ℕ) (hn : 0 < n) :
    Tendsto (fun r : ℝ => valueV (squeezedCM n r)) atTop (nhds 0) :=
  x8_main n hn

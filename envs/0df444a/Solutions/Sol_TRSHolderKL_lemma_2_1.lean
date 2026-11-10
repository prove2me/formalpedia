-- Prove2me | solution 1 for TRSHolderKL.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T05:49:18.769852+00:00
-- url     : https://prove2.me/submissions/688f21c8-1222-4a61-a8a5-1671f4dbb790

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_f
import Definitions.Def_TRSHolderKL_S0
import Definitions.Def_TRSHolderKL_lam1
import Definitions.Def_TRSHolderKL_ftilde
import Definitions.Def_TRSHolderKL_S1

open scoped InnerProductSpace
open RBMSensitivity (E)

open TRSHolderKL in
theorem solution {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hA0 : A ≠ 0) (b : E n) (hlam : lam1 A < 0) :
    (∀ x ∈ S0 A b, ‖x‖ = 1) ∧ (∀ x ∈ S0 A b, ftilde A b x = f A b x) ∧
      S0 A b = S1 A b ∩ {x | ‖x‖ = 1} := by
  have hne : (spectrum ℝ A).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have : lam1 A = 0 := by unfold lam1; rw [h, Real.sInf_empty]
    linarith
  have hmem : lam1 A ∈ spectrum ℝ A := hne.csInf_mem (Matrix.finite_spectrum A)
  rw [← Matrix.spectrum_toLin'] at hmem
  obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hmem).exists_hasEigenvector
  obtain ⟨hv1, hv0⟩ := Module.End.hasEigenvector_iff.mp hv
  rw [Module.End.mem_eigenspace_iff] at hv1
  have hTu0 : Matrix.toEuclideanLin A (WithLp.toLp 2 v) = lam1 A • WithLp.toLp 2 v := by
    rw [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp, ← Matrix.toLin'_apply, hv1, WithLp.toLp_smul]
  have hu0ne : (WithLp.toLp 2 v : E n) ≠ 0 := by
    intro h
    apply hv0
    have := congrArg WithLp.ofLp h
    simpa using this
  obtain ⟨u, hu⟩ : ∃ u : E n, u = ‖(WithLp.toLp 2 v : E n)‖⁻¹ • (WithLp.toLp 2 v : E n) := ⟨_, rfl⟩
  have hu1 : ‖u‖ = 1 := by rw [hu]; exact norm_smul_inv_norm hu0ne
  have hTu : Matrix.toEuclideanLin A u = lam1 A • u := by
    rw [hu, map_smul, hTu0, smul_comm]
  have hsym : ∀ x y : E n, ⟪Matrix.toEuclideanLin A x, y⟫_ℝ = ⟪x, Matrix.toEuclideanLin A y⟫_ℝ :=
    Matrix.isHermitian_iff_isSymmetric.mp hA
  have huu : ⟪u, u⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hu1]; norm_num
  have hfexp : ∀ (y : E n) (t : ℝ), f A b (y + t • u) =
      f A b y + 2 * t * (lam1 A * ⟪y, u⟫_ℝ - ⟪b, u⟫_ℝ) + lam1 A * t ^ 2 := by
    intro y t
    unfold f
    have h1 : ⟪u, Matrix.toEuclideanLin A y⟫_ℝ = lam1 A * ⟪y, u⟫_ℝ := by
      rw [← hsym, hTu, real_inner_smul_left, real_inner_comm]
    rw [map_add, map_smul, hTu]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, h1, huu]
    ring
  have hft : ∀ y : E n, ftilde A b y = f A b y + lam1 A * (1 - ‖y‖ ^ 2) := by
    intro y
    unfold ftilde f
    have h1 : Matrix.toEuclideanLin (1 : Matrix (Fin n) (Fin n) ℝ) y = y := by
      rw [Matrix.toEuclideanLin_apply, Matrix.one_mulVec, WithLp.toLp_ofLp]
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, h1, inner_sub_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have key : ∀ y : E n, ‖y‖ ≤ 1 → ∃ z : E n, ‖z‖ ≤ 1 ∧ f A b z ≤ ftilde A b y := by
    intro y hy
    obtain ⟨p, hp⟩ : ∃ p, p = ⟪y, u⟫_ℝ := ⟨_, rfl⟩
    have hdisc : 0 ≤ p ^ 2 + 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
    obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt (p ^ 2 + 1 - ‖y‖ ^ 2) := ⟨_, rfl⟩
    have hs : s ^ 2 = p ^ 2 + 1 - ‖y‖ ^ 2 := by rw [hsdef]; exact Real.sq_sqrt hdisc
    have hs0 : 0 ≤ s := by rw [hsdef]; exact Real.sqrt_nonneg _
    have habs : |p| ≤ s := by
      rw [hsdef]
      exact Real.abs_le_sqrt (by nlinarith [norm_nonneg y])
    have hsp : p ≤ s := (abs_le.mp habs).2
    have hsp' : -p ≤ s := by linarith [(abs_le.mp habs).1]
    have hnorm : ∀ t : ℝ, ‖y + t • u‖ ^ 2 = ‖y‖ ^ 2 + 2 * t * p + t ^ 2 := by
      intro t
      rw [norm_add_sq_real, real_inner_smul_right, norm_smul, hu1, Real.norm_eq_abs, mul_one,
        sq_abs, ← hp]
      ring
    obtain ⟨t, ht, htb⟩ : ∃ t : ℝ, t ^ 2 + 2 * t * p + ‖y‖ ^ 2 = 1 ∧ 0 ≤ t * ⟪b, u⟫_ℝ := by
      by_cases hb : 0 ≤ ⟪b, u⟫_ℝ
      · exact ⟨-p + s, by nlinarith [hs], mul_nonneg (by linarith) hb⟩
      · push_neg at hb
        exact ⟨-p - s, by nlinarith [hs], mul_nonneg_of_nonpos_of_nonpos (by linarith) hb.le⟩
    refine ⟨y + t • u, ?_, ?_⟩
    · have h1 : ‖y + t • u‖ ^ 2 = 1 := by rw [hnorm]; linarith
      have h2 : ‖y + t • u‖ = 1 := by
        have := (sq_eq_sq₀ (norm_nonneg (y + t • u)) zero_le_one).mp (by rw [h1]; norm_num)
        exact this
      exact h2.le
    · rw [hfexp, hft, ← hp]
      have e : lam1 A * (1 - ‖y‖ ^ 2) = lam1 A * t ^ 2 + 2 * t * (lam1 A * p) := by
        rw [← ht]; ring
      linarith
  have hS0norm : ∀ x ∈ S0 A b, ‖x‖ = 1 := by
    rintro x ⟨hx1, hxmin⟩
    by_contra hne1
    have hlt : ‖x‖ < 1 := lt_of_le_of_ne hx1 hne1
    obtain ⟨z, hz1, hz⟩ := key x hx1
    have h1 := hxmin z hz1
    rw [hft] at hz
    have h2 : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
    have h3 : lam1 A * (1 - ‖x‖ ^ 2) < 0 := mul_neg_of_neg_of_pos hlam h2
    linarith
  have hS0eq : ∀ x ∈ S0 A b, ftilde A b x = f A b x := by
    intro x hx
    rw [hft, hS0norm x hx]
    ring
  refine ⟨hS0norm, hS0eq, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨hx1, hxmin⟩ := hx
    refine ⟨⟨hx1, fun y hy => ?_⟩, hS0norm x ⟨hx1, hxmin⟩⟩
    obtain ⟨z, hz1, hz⟩ := key y hy
    rw [hS0eq x ⟨hx1, hxmin⟩]
    exact le_trans (hxmin z hz1) hz
  · rintro ⟨⟨hx1, hxmin⟩, hxn⟩
    have hxn' : ‖x‖ = 1 := hxn
    refine ⟨hx1, fun y hy => ?_⟩
    have h1 := hxmin y hy
    rw [hft, hft, hxn'] at h1
    have h2 : 0 ≤ 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
    have h3 : lam1 A * (1 - ‖y‖ ^ 2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hlam.le h2
    nlinarith

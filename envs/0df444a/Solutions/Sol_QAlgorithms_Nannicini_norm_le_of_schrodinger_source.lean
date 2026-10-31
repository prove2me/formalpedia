-- Prove2me | solution 1 for QAlgorithms.Nannicini.norm_le_of_schrodinger_source
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-30T14:35:02.741998+00:00
-- url     : https://prove2.me/submissions/938b595b-a884-4d34-a58e-a09759a37f35

import Definitions.Def_QAlgorithms_Defs_Adiabatic

set_option autoImplicit false

open QAlgorithms

theorem solution {ι : Type*} [Fintype ι] (H : ℝ → Matrix ι ι ℂ)
    (hH : ∀ s ∈ Set.Icc (0 : ℝ) 1, (H s).IsHermitian) (T : ℝ)
    (f h : ℝ → EuclideanSpace ℂ ι)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt f (Complex.I • (T : ℂ) • act (H s) (f s) + h s) (Set.Icc 0 1) s)
    (M : ℝ) (hM : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖h s‖ ≤ M) : ‖f 1‖ ≤ ‖f 0‖ + M := by
  classical
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 h0)
  -- the unitary part does not contribute: `Re ⟪z, i T H z⟫ = 0`
  have hre : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ z : EuclideanSpace ℂ ι,
      inner ℝ z (Complex.I • (T : ℂ) • act (H s) z) = 0 := by
    intro s hs z
    have hsym : (Matrix.toEuclideanLin (H s)).IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr (hH s hs)
    have hreal := hsym.coe_re_inner_apply_self z
    have hact : act (H s) z = Matrix.toEuclideanLin (H s) z := rfl
    have hri : inner ℝ z (Complex.I • (T : ℂ) • act (H s) z) =
        (inner ℂ z (Complex.I • (T : ℂ) • act (H s) z)).re := by
      rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Complex.inner, mul_comm]
    rw [hri, inner_smul_right, inner_smul_right, hact, ← inner_conj_symm,
      ← hreal]
    simp
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set g : ℝ → ℝ := fun s => Real.sqrt (‖f s‖ ^ 2 + ε ^ 2) with hg
  have hgpos : ∀ s, 0 < ‖f s‖ ^ 2 + ε ^ 2 := fun s => by positivity
  have hgd : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt g
      (2 * inner ℝ (f s) (Complex.I • (T : ℂ) • act (H s) (f s) + h s) /
        (2 * Real.sqrt (‖f s‖ ^ 2 + ε ^ 2))) (Set.Icc 0 1) s := fun s hs =>
    (((hf s hs).norm_sq).add_const (ε ^ 2)).sqrt (hgpos s).ne'
  have hgb : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      2 * inner ℝ (f s) (Complex.I • (T : ℂ) • act (H s) (f s) + h s) /
        (2 * Real.sqrt (‖f s‖ ^ 2 + ε ^ 2)) ≤ M := by
    intro s hs
    have hsq : 0 < Real.sqrt (‖f s‖ ^ 2 + ε ^ 2) := Real.sqrt_pos.mpr (hgpos s)
    rw [div_le_iff₀ (by positivity), inner_add_right, hre s hs, zero_add]
    have h1 : inner ℝ (f s) (h s) ≤ ‖f s‖ * ‖h s‖ := real_inner_le_norm _ _
    have h2 : ‖f s‖ ≤ Real.sqrt (‖f s‖ ^ 2 + ε ^ 2) := by
      rw [Real.le_sqrt (norm_nonneg _) (hgpos s).le]; nlinarith
    have h3 : ‖f s‖ * ‖h s‖ ≤ Real.sqrt (‖f s‖ ^ 2 + ε ^ 2) * M :=
      mul_le_mul h2 (hM s hs) (norm_nonneg _) hsq.le
    linarith
  have hmain := image_le_of_deriv_right_le_deriv_boundary (a := 0) (b := 1) (f := g)
    (fun s hs => (hgd s hs).continuousWithinAt)
    (fun s hs => (hgd s (Set.Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs))
    (B := fun s => g 0 + M * s) (B' := fun _ => M) (by simp)
    (by fun_prop)
    (fun s _ => by simpa using ((hasDerivAt_id s).const_mul M).const_add (g 0) |>.hasDerivWithinAt)
    (fun s hs => hgb s (Set.Ico_subset_Icc_self hs)) h1
  simp only [mul_one] at hmain
  have hf1 : ‖f 1‖ ≤ g 1 := by
    rw [hg, Real.le_sqrt (norm_nonneg _) (hgpos 1).le]; nlinarith
  have hg0 : g 0 ≤ ‖f 0‖ + ε := by
    rw [hg, Real.sqrt_le_iff]
    exact ⟨by positivity, by nlinarith [norm_nonneg (f 0)]⟩
  linarith

-- Prove2me | solution 1 for ProjectiveMeasurementEquilibration.relEntropy_pinching_eq_entropy_sub
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T20:16:03.873988+00:00
-- url     : https://prove2.me/submissions/0c15af08-7dc8-4556-b636-806f84d7f809

import Definitions.Def_pme_quantum_basics
import Theorems.Thm_ProjectiveMeasurementEquilibration_commute_iff_pinching_eq
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

open Matrix ProjectiveMeasurementEquilibration
open scoped ComplexOrder

private lemma projection_facts {n : Type} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    (∀ x, (eigenproj hX x).IsHermitian) ∧
    (∀ x, eigenproj hX x * eigenproj hX x = eigenproj hX x) ∧
    (∑ x ∈ eigenvalueSet hX, eigenproj hX x) = 1 := by
  classical
  let U : Matrix n n ℂ := hX.eigenvectorUnitary
  let D : ℝ → Matrix n n ℂ := fun x =>
    diagonal (fun i => if hX.eigenvalues i = x then (1 : ℂ) else 0)
  have heq (x : ℝ) : eigenproj hX x = U * D x * Uᴴ := rfl
  have hD (x : ℝ) : (D x).PosSemidef := by
    apply PosSemidef.diagonal
    intro i
    dsimp [D]
    split_ifs <;> simp
  have hDD (x : ℝ) : D x * D x = D x := by
    dsimp [D]
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> simp
  refine ⟨fun x => ?_, fun x => ?_, ?_⟩
  · rw [heq]
    exact ((hD x).mul_mul_conjTranspose_same U).1
  · rw [heq]
    calc
      (U * D x * Uᴴ) * (U * D x * Uᴴ) = U * (D x * (Uᴴ * U) * D x) * Uᴴ := by
        simp only [mul_assoc]
      _ = U * D x * Uᴴ := by
        have hu : Uᴴ * U = 1 := Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.property
        rw [hu, mul_one, hDD]
  · have hdiag : (∑ x ∈ eigenvalueSet hX, D x) = 1 := by
      ext i j
      by_cases hij : i = j
      · subst j
        have hmem : hX.eigenvalues i ∈ eigenvalueSet hX :=
          Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
        simp [D, Matrix.sum_apply, hmem]
      · simp [D, Matrix.sum_apply, hij]
    simp only [heq]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hdiag, mul_one]
    exact Unitary.mul_star_self_of_mem hX.eigenvectorUnitary.property

private lemma support_pinching {n : Type} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} (hX : X.IsHermitian) (ρ : Matrix n n ℂ)
    (hρ : ρ.PosSemidef) : SupportLE ρ (pinching hX ρ) := by
  classical
  obtain ⟨hHerm, _, hsum⟩ := projection_facts hX
  intro v hv
  have hq (x : ℝ) :
      star (eigenproj hX x *ᵥ v) ⬝ᵥ (ρ *ᵥ (eigenproj hX x *ᵥ v)) =
        star v ⬝ᵥ ((eigenproj hX x * ρ * eigenproj hX x) *ᵥ v) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
    rw [star_mulVec, (hHerm x).eq]
    simp only [← dotProduct_mulVec]
  have hzero : (∑ x ∈ eigenvalueSet hX,
      star (eigenproj hX x *ᵥ v) ⬝ᵥ (ρ *ᵥ (eigenproj hX x *ᵥ v))) = 0 := by
    simp_rw [hq]
    rw [← dotProduct_sum, ← sum_mulVec]
    change star v ⬝ᵥ (pinching hX ρ *ᵥ v) = 0
    rw [hv, dotProduct_zero]
  have heach : ∀ x ∈ eigenvalueSet hX, ρ *ᵥ (eigenproj hX x *ᵥ v) = 0 := by
    intro x hx
    apply (hρ.dotProduct_mulVec_zero_iff _).mp
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun y _ => hρ.dotProduct_mulVec_nonneg _)).mp hzero x hx
  calc
    ρ *ᵥ v = ρ *ᵥ ((∑ x ∈ eigenvalueSet hX, eigenproj hX x) *ᵥ v) := by
      rw [hsum, one_mulVec]
    _ = 0 := by
      rw [sum_mulVec, mulVec_sum]
      exact Finset.sum_eq_zero heach

private lemma trace_pinching {n : Type} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} (hX : X.IsHermitian) (ρ B : Matrix n n ℂ)
    (hB : X * B = B * X) : (pinching hX ρ * B).trace = (ρ * B).trace := by
  classical
  obtain ⟨_, hPP, hsum⟩ := projection_facts hX
  have hcomm (x : ℝ) : Commute (eigenproj hX x) B := by
    have heq : eigenproj hX x = cfc (fun t : ℝ => if t = x then 1 else 0) X := by
      have hf : (fun i => if hX.eigenvalues i = x then (1 : ℂ) else 0) =
          (RCLike.ofReal ∘ (fun t : ℝ => if t = x then 1 else 0) ∘ hX.eigenvalues) := by
        funext i
        dsimp [Function.comp_def]
        split_ifs <;> simp
      rw [hX.cfc_eq]
      simp only [Matrix.IsHermitian.cfc, eigenproj, hf, Unitary.conjStarAlgAut_apply]
    rw [heq]
    exact (show Commute X B from hB).cfc_real _
  change ((∑ x ∈ eigenvalueSet hX, eigenproj hX x * ρ * eigenproj hX x) * B).trace = _
  rw [Finset.sum_mul, Matrix.trace_sum]
  have ht (x : ℝ) : (eigenproj hX x * ρ * eigenproj hX x * B).trace =
      (ρ * B * eigenproj hX x).trace := by
    rw [mul_assoc (eigenproj hX x * ρ), (hcomm x).eq,
      ← mul_assoc, Matrix.trace_mul_cycle, ← mul_assoc, hPP, Matrix.trace_mul_cycle]
    rw [Matrix.trace_mul_cycle]
  simp_rw [ht]
  rw [← Matrix.trace_sum, ← Finset.mul_sum, hsum, mul_one]

private lemma pinching_fixed {n : Type} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} (hX : X.IsHermitian) (A : Matrix n n ℂ) :
    pinching hX (pinching hX A) = pinching hX A := by
  classical
  let G := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hX.eigenvectorUnitary
  let F := G.symm
  let D : ℝ → Matrix n n ℂ := fun x =>
    diagonal (fun i => if hX.eigenvalues i = x then (1 : ℂ) else 0)
  have heig (x : ℝ) : F (eigenproj hX x) = D x := by
    change G.symm (G (D x)) = D x
    exact G.symm_apply_apply (D x)
  have hentry (A : Matrix n n ℂ) (i j : n) : F (pinching hX A) i j =
      if hX.eigenvalues i = hX.eigenvalues j then F A i j else 0 := by
    have hpinch : F (pinching hX A) =
        ∑ x ∈ eigenvalueSet hX, D x * F A * D x := by
      simp only [pinching, map_sum, map_mul, heig]
    rw [hpinch]
    have hmem : hX.eigenvalues j ∈ eigenvalueSet hX :=
      Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
    simp [D, Matrix.sum_apply, hmem, eq_comm]
  have hidem (A : Matrix n n ℂ) : pinching hX (pinching hX A) = pinching hX A := by
    apply F.injective
    change F (pinching hX (pinching hX A)) = F (pinching hX A)
    ext i j
    simp only [hentry]
    by_cases hij : hX.eigenvalues i = hX.eigenvalues j <;> simp [hij]
  exact hidem A

theorem solution {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}
    (hX : X.IsHermitian) (ρ : Matrix n n ℂ) (hρ : IsDensityMatrix ρ) :
    relEntropy ρ (pinching hX ρ) =
      ((vonNeumannEntropy (pinching hX ρ) - vonNeumannEntropy ρ : ℝ) : EReal) := by
  have hfixed : X * pinching hX ρ = pinching hX ρ * X := by
    apply (commute_iff_pinching_eq hX _).mpr
    exact pinching_fixed hX ρ
  have hlog : X * matrixLog (pinching hX ρ) = matrixLog (pinching hX ρ) * X :=
    ((show Commute (pinching hX ρ) X from hfixed.symm).cfc_real Real.log).symm.eq
  rw [relEntropy, if_pos (support_pinching hX ρ hρ.1)]
  congr 1
  rw [mul_sub, Matrix.trace_sub, Complex.sub_re]
  unfold vonNeumannEntropy
  rw [trace_pinching hX ρ _ hlog]
  ring

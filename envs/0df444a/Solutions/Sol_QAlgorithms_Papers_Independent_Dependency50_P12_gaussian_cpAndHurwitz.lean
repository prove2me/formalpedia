-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P12.gaussian_cpAndHurwitz
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T07:36:00.891196+00:00
-- url     : https://prove2.me/submissions/f7c3ac04-7b2e-4552-8d79-8729e93df4b7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P12

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.Frobenius

open Set

open QAlgorithms.Papers.Independent.Dependency50.P12

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] Classical.propDecidable Classical.decEq

open Coordinates

open QAlgorithms.Papers.Independent.Information100

attribute [local instance] QAlgorithms.Papers.Independent.Dependency50.P12.inheritedSubalgebraTopologicalAddGroup


theorem g55a_cp_eq (r gamma : ℝ) : gaussianCP r gamma =
    !![((gamma/2 : ℝ) : ℂ), Complex.I * ((gamma/2 : ℝ) : ℂ);
      -Complex.I * ((gamma/2 : ℝ) : ℂ), ((gamma/2 : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gaussianCP, gaussianD, gaussianA, ccrOmega, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.diagonal_apply, Matrix.vecMul_diagonal] <;> push_cast <;> ring

theorem g55a_scale_pair {X : Type*} [AddCommGroup X] [Module ℝ X] (W : Set X)
    (hW : ∀ c : ℝ, 0 ≤ c → ∀ x ∈ W, c • x ∈ W)
    (P Q : X) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ({a • P, b • Q} : Set X) ⊆ W ↔ ({P, Q} : Set X) ⊆ W := by
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := hW a⁻¹ (inv_nonneg.2 ha.le) _ h1
      rwa [smul_smul, inv_mul_cancel₀ ha.ne', one_smul] at this
    · have := hW b⁻¹ (inv_nonneg.2 hb.le) _ h2
      rwa [smul_smul, inv_mul_cancel₀ hb.ne', one_smul] at this
  · rintro ⟨h1, h2⟩
    exact ⟨hW a ha.le _ h1, hW b hb.le _ h2⟩

theorem g55a_gG (r gamma a b : ℝ) :
    gaussianG (a*r) (b*gamma) = {a • squeezeMoment r, b • dampingMoment gamma} := by
  have h1 : squeezeMoment (a*r) = a • squeezeMoment r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [squeezeMoment, momentMap, Matrix.diagonal_apply] <;> ring
  have h2 : dampingMoment (b*gamma) = b • dampingMoment gamma := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dampingMoment, momentMap, gaussianD, Matrix.diagonal_apply] <;> ring
  simp [gaussianG, h1, h2]

/-- arXiv:2608.27330v1, PDF pp.38--39, Section 6.3 spectral/CP assertion.
No infinite-dimensional oscillator semigroup is asserted. Spectra are recorded
with multiplicity by characteristic polynomials; the threshold is strict. -/
theorem solution (r gamma : ℝ) (hg : 0 ≤ gamma) :
    (gaussianCP r gamma).charpoly = Polynomial.X * (Polynomial.X - Polynomial.C (gamma : ℂ)) ∧
    ((gaussianCP r gamma).PosSemidef ↔ 0 ≤ gamma) ∧
    (gaussianA r gamma).charpoly =
      (Polynomial.X - Polynomial.C (-gamma/2 + |r|)) *
      (Polynomial.X - Polynomial.C (-gamma/2 - |r|)) ∧
    (Hurwitz (gaussianA r gamma) ↔ 2 * |r| < gamma) ∧
    (∀ a b : ℝ, 0 < a → 0 < b →
      LieSubalgebra.lieSpan ℝ (Matrix (Fin 6) (Fin 6) ℝ) (gaussianG (a*r) (b*gamma)) =
        LieSubalgebra.lieSpan ℝ (Matrix (Fin 6) (Fin 6) ℝ) (gaussianG r gamma) ∧
      minimalWedge (gaussianG (a*r) (b*gamma)) = minimalWedge (gaussianG r gamma)) := by
  have hdetA : ∀ z : ℂ, ((gaussianA r gamma).map Complex.ofReal - z • 1).det =
      (((-gamma/2 - r : ℝ) : ℂ) - z) * (((-gamma/2 + r : ℝ) : ℂ) - z) := by
    intro z
    rw [Matrix.det_fin_two]
    simp [gaussianA, Matrix.diagonal_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.charpoly_fin_two, g55a_cp_eq, Matrix.trace_fin_two, Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    have ht : ((gamma/2 : ℝ) : ℂ) + ((gamma/2 : ℝ) : ℂ) = (gamma : ℂ) := by push_cast; ring
    have hd : ((gamma/2 : ℝ) : ℂ) * ((gamma/2 : ℝ) : ℂ) -
        Complex.I * ((gamma/2 : ℝ) : ℂ) * (-Complex.I * ((gamma/2 : ℝ) : ℂ)) = 0 := by
      ring_nf; rw [Complex.I_sq]; ring
    rw [ht, hd, Polynomial.C_0]; ring
  · refine ⟨fun _ => hg, fun _ => ?_⟩
    set s : ℂ := ((Real.sqrt (gamma/2) : ℝ) : ℂ)
    have hs1 : s * s = (gamma : ℂ) / 2 := by
      simp only [s, ← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith : (0:ℝ) ≤ gamma/2)]
      push_cast; ring
    have hc : (starRingEnd ℂ) s = s := by simp [s]
    let B : Matrix (Fin 2) (Fin 2) ℂ := !![s, Complex.I * s; 0, 0]
    have : gaussianCP r gamma = Bᴴ * B := by
      rw [g55a_cp_eq]
      ext i j
      fin_cases i <;> fin_cases j
      · simp [B, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, hc]
        linear_combination -hs1
      · simp [B, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, hc]
        linear_combination -Complex.I * hs1
      · simp [B, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, hc]
        linear_combination -Complex.I * hs1
      · simp [B, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, hc]
        linear_combination -hs1 + s * s * Complex.I_sq
    rw [this]
    exact Matrix.posSemidef_conjTranspose_mul_self B
  · rw [show gaussianA r gamma = Matrix.diagonal ![-gamma/2-r, -gamma/2+r] from rfl,
      Matrix.charpoly_diagonal, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rcases abs_cases r with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
    · ring
    · rw [show -gamma/2 + -r = -gamma/2 - r by ring, show -gamma/2 - -r = -gamma/2 + r by ring]
  · unfold Hurwitz
    constructor
    · intro hH
      have h1 := hH ((-gamma/2 - r : ℝ) : ℂ) (by rw [hdetA]; simp)
      have h2 := hH ((-gamma/2 + r : ℝ) : ℂ) (by rw [hdetA]; simp)
      simp only [Complex.ofReal_re] at h1 h2
      rcases abs_cases r with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
    · intro hlt z hz
      rw [hdetA] at hz
      rcases mul_eq_zero.1 hz with h | h
      · rw [sub_eq_zero] at h; rw [← h]; simp only [Complex.ofReal_re]
        rcases abs_cases r with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hlt <;> linarith
      · rw [sub_eq_zero] at h; rw [← h]; simp only [Complex.ofReal_re]
        rcases abs_cases r with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hlt <;> linarith
  · intro a b ha hb
    rw [g55a_gG]
    have hspan : LieSubalgebra.lieSpan ℝ (Matrix (Fin 6) (Fin 6) ℝ)
        {a • squeezeMoment r, b • dampingMoment gamma} =
        LieSubalgebra.lieSpan ℝ (Matrix (Fin 6) (Fin 6) ℝ) (gaussianG r gamma) := by
      apply le_antisymm
      · rw [LieSubalgebra.lieSpan_le]
        refine (g55a_scale_pair _ (fun c _ x hx => LieSubalgebra.smul_mem _ c hx) _ _ a b ha hb).2 ?_
        exact LieSubalgebra.subset_lieSpan
      · rw [LieSubalgebra.lieSpan_le]
        refine (g55a_scale_pair _ (fun c _ x hx => LieSubalgebra.smul_mem _ c hx) _ _ a b ha hb).1 ?_
        exact LieSubalgebra.subset_lieSpan
    refine ⟨hspan, ?_⟩
    ext x
    unfold minimalWedge
    rw [hspan]
    refine and_congr Iff.rfl (forall_congr' fun W => imp_congr_right fun hW => ?_)
    rw [g55a_scale_pair W (fun c hc x hx => hW.2.1.2.2 c hc x hx) _ _ a b ha hb]
    rfl


end


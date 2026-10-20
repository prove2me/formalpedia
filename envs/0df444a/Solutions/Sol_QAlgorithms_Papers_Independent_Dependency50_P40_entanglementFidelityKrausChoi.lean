-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P40.entanglementFidelityKrausChoi
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T02:39:00.334694+00:00
-- url     : https://prove2.me/submissions/76c6c691-90cc-4af8-928d-acbf459cde29

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P40

open scoped ComplexConjugate ComplexOrder Matrix

open QAlgorithms.Papers.Independent.Information100.P34 (dyad)


lemma g53c_sum3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℂ) :
    ∑ x, ∑ y, ∑ z, f x y z = ∑ z, ∑ x, ∑ y, f x y z := by
  calc ∑ x, ∑ y, ∑ z, f x y z = ∑ x, ∑ z, ∑ y, f x y z := by
        refine Finset.sum_congr rfl fun x _ => ?_
        exact Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ y, f x y z := Finset.sum_comm

lemma g53c_fid {h a m : ℕ} (psi : EuclideanSpace ℂ (Fin a × Fin h))
    (B : Fin m → Matrix (Fin h) (Fin h) ℂ) :
    complexQuadraticForm psi (idTensorSuperop (krausApply B) (pureDensity psi)) =
      ∑ i, ((traceLeft (pureDensity psi)) * B i).trace *
        conj (((traceLeft (pureDensity psi)) * B i).trace) := by
  set u : Fin m → Fin a × Fin h → ℂ := fun i p => ∑ x, B i p.2 x * psi (p.1, x) with hu
  have hX : ∀ p q : Fin a × Fin h,
      idTensorSuperop (krausApply B) (pureDensity psi) p q = ∑ i, u i p * conj (u i q) := by
    intro p q
    simp only [idTensorSuperop, krausApply, Matrix.of_apply, Matrix.sum_apply, pureDensity, hu]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, map_sum, map_mul,
      Complex.star_def, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  have hw : ∀ i, ((traceLeft (pureDensity psi)) * B i).trace = ∑ p, conj (psi p) * u i p := by
    intro i
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, traceLeft, pureDensity, Matrix.of_apply,
      hu, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
    rw [g53c_sum3]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  simp only [complexQuadraticForm, hX, hw, map_sum, map_mul, Complex.conj_conj]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [g53c_sum3]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

/-- PDF pp.2–3, (6), (16)–(17): general-input entanglement fidelity.
The Kraus identity is standard background attributed to Schumacher [12]. -/
theorem solution {h a m : ℕ} (hh : 0 < h)
    (rho : Matrix (Fin h) (Fin h) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin h)) (hpsi : IsPurification rho psi)
    (B : Fin m → Matrix (Fin h) (Fin h) ℂ) (hB : IsKrausFamily B) :
    purificationFidelity psi (krausApply B) = ∑ i, Complex.normSq ((rho * B i).trace) ∧
    purificationFidelity psi (krausApply B) =
      (∑ i, (inner ℂ (operatorKet rho) (operatorKet (B i))) *
        (inner ℂ (operatorKet (B i)) (operatorKet rho))).re ∧
    purificationFidelity psi (krausApply B) = (complexQuadraticForm (operatorKet rho) (krausChoi B)).re := by
  obtain ⟨_, hrho'⟩ := hpsi
  have hF : purificationFidelity psi (krausApply B) =
      (∑ i, (rho * B i).trace * conj ((rho * B i).trace)).re := by
    rw [purificationFidelity, g53c_fid, hrho']
  have hherm : ∀ x y, conj (rho x y) = rho y x := by
    intro x y
    have := congrFun (congrFun hrho.1.1 y) x
    simpa [Matrix.conjTranspose_apply] using this
  have hin : ∀ i, inner ℂ (operatorKet rho) (operatorKet (B i)) = (rho * B i).trace := by
    intro i
    simp only [PiLp.inner_apply, operatorKet, RCLike.inner_apply, Fintype.sum_prod_type,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, hherm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  have hin2 : ∀ i, inner ℂ (operatorKet (B i)) (operatorKet rho) = conj ((rho * B i).trace) := by
    intro i
    rw [← hin i, inner_conj_symm]
  have hQ : complexQuadraticForm (operatorKet rho) (krausChoi B) =
      ∑ i, (rho * B i).trace * conj ((rho * B i).trace) := by
    simp only [← hin]
    simp only [complexQuadraticForm, krausChoi, dyad, Matrix.sum_apply, PiLp.inner_apply,
      RCLike.inner_apply, Finset.mul_sum, Finset.sum_mul, map_sum, map_mul, Complex.conj_conj]
    rw [g53c_sum3]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [operatorKet]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hF, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.mul_conj, Complex.ofReal_re]
  · rw [hF]; simp only [hin, hin2]
  · rw [hF, hQ]


end

